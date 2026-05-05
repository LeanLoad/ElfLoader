# Background: FFI in Lean 4

Survey of how Lean 4 talks to C/C++, distilled from the Lean reference
manual, the Lean source tree (`third_party/lean4`), and several
representative open-source projects.

## What Lean's FFI is

Lean 4 has a stable-ish C ABI for calling external symbols from Lean
and exposing Lean symbols to external code. Two attributes do most of
the work:

- `@[extern "c_name"] def f ... := ...` — bind `f` to the C symbol
  `c_name`. Compiled code calls the symbol; the kernel still sees the
  Lean body for elaboration and proofs.
- `@[export c_name] def f ... := ...` — give a Lean definition an
  unmangled C name so external code can call it.

The reference manual is upfront that the FFI was "designed for internal
use in Lean and should be considered unstable." In practice it has been
remarkably stable since Lean 4.0, and dozens of community projects
depend on it.

## Three styles for binding to C

1. **Separate `ffi.cpp` (or `ffi.c`) compiled by Lake.** The most
   common style. Lean side has `@[extern]` declarations; C side has
   `extern "C" lean_object * c_name(...)`. Lake builds the C as a
   static + dynamic library and links it. Examples: `SampCert`, the
   GLFW tutorial, most of the Lean runtime itself.
2. **Inline C via `alloy`** (`tydeu/lean4-alloy`). Lets you write
   `alloy c extern def myAdd (x y : UInt32) : UInt32 := { return x + y; }`
   directly in a `.lean` file. Lake's module-facets feature builds the
   shim as part of the module. Best for small, purpose-built shims
   co-located with the Lean declaration. Caveat: the same-module
   interpreter restriction (see "Pitfalls") still applies.
3. **`ctypes`-style dynamic loading** (`alexf91/lean4-ctypes`). Loads
   a shared object at runtime and calls into it without static
   bindings. Useful for prototyping or for binding libraries you do
   not want to compile against. Higher overhead per call.

For systems work — wrapping `libc`, `libelf`, `libuv`, anything with
opaque handles or ownership semantics — style 1 is the default. Style
2 is good for one-off shims.

## ABI essentials

Every Lean value crosses the boundary as `lean_object *` unless it is
a primitive (`uint*_t`, `size_t`, `double`, `uint32_t` for `Char`).
The rules below are the difference between code that runs and code
that double-frees.

### Reference counting is your responsibility

Lean uses reference counting, not GC. Every owned reference must
eventually be released; every duplicate you keep must be `lean_inc`'d.

- `lean_inc(o)` — bump the refcount. No-op on scalars, safe to call
  unconditionally.
- `lean_dec(o)` — drop the refcount. May free the object and recurse
  into its fields. No-op on scalars.
- `lean_box(n)` — pack a `size_t` into a tagged scalar:
  `(n << 1) | 1`. `lean_unbox(o)` reverses it. Defined inline in
  `third_party/lean4/src/include/lean/lean.h:312-314`.

Gotcha: `lean_apply_n` consumes its arguments. If you intend to use a
value past a call to `lean_apply_*`, `lean_inc` it first. The `prob_While`
implementation in `third_party/SampCert/ffi.cpp:32` shows this clearly
— `condition`, `body`, and `state` all get explicit `lean_inc` calls
across loop iterations.

### Owned vs. borrowed (`@&`)

By default, every `lean_object *` parameter is **owned** — the C
function inherits a refcount token and must consume it (pass it
onward to a consuming call, or `lean_dec` it).

Mark a Lean parameter `@&` to make it **borrowed** — the C function
gets a non-owning reference, must not `lean_dec` it, and the caller
remains responsible. The corresponding C parameter is typically typed
`b_lean_obj_arg`.

```lean
@[extern "lean_io_prim_handle_read"]
opaque read (h : @& Handle) (bytes : USize) : IO ByteArray
```

(`third_party/lean4/src/Init/System/IO.lean:847`.) The `Handle` is
borrowed, the returned `ByteArray` is owned.

Mismatching the Lean annotation and the C body causes leaks (annotated
borrowed, C never decs) or double-frees (annotated owned, C also
decs). **They must agree.**

### IO actions take a "world" argument

A Lean signature `foo : T → IO U` becomes a C function
`lean_object * foo(lean_object * x, lean_object * world)`. Ignore the
world argument. Return either:

- `lean_io_result_mk_ok(value)` on success, or
- `lean_io_result_mk_error(err_obj)` on failure (typically build
  `err_obj` with `lean_mk_io_user_error(lean_mk_string(...))`).

Same for `BaseIO`.

### Type translation cheat sheet

| Lean type                 | C type                  |
| ------------------------- | ----------------------- |
| `UInt8`...`UInt64`,`USize`| `uint8_t`...`size_t`    |
| `Int8`...`Int64`,`ISize`  | `int8_t`...`ssize_t`    |
| `Char`                    | `uint32_t`              |
| `Float`                   | `double`                |
| `Bool`                    | `uint8_t`               |
| `Nat`, `Int`              | `lean_object *` (boxed bignum or tagged scalar — check with `lean_is_scalar`) |
| `String`                  | `lean_object *` (use `lean_string_cstr` for `const char *`) |
| `ByteArray`               | `lean_object *` (use `lean_sarray_cptr` for `uint8_t *`) |
| custom inductive          | `lean_object *` per the runtime layout |
| `Prop`, universe levels   | erased or `lean_box(0)` |

C `struct` and `union` cannot cross the boundary by value. Wrap them in
opaque external objects (next section) or marshal field-by-field.

## Opaque foreign types

For file descriptors, `void *` from `mmap`, parsed state, libuv loops
— anything with a non-trivial lifetime — use Lean's **external object**
mechanism.

The shape is consistent across every project that does it (Lean core's
`IO.FS.Handle`, the GLFW tutorial's `GLFWwindow`, raylib bindings,
socket bindings):

```c
#include <lean/lean.h>

typedef struct { /* whatever your foreign data is */ int fd; } my_data;

static void my_finalize(void * p) {
    my_data * d = (my_data *) p;
    /* close / munmap / free / etc. */
    free(d);
}
static void my_foreach(void * p, b_lean_obj_arg f) {
    /* If the data owns nested lean_object *s, apply f to each.
       For a raw fd or pointer, no-op. */
    (void)p; (void)f;
}

static lean_external_class * g_class = NULL;
static lean_external_class * my_class(void) {
    if (!g_class)
        g_class = lean_register_external_class(my_finalize, my_foreach);
    return g_class;
}

extern "C" lean_object * my_make(/* ... */, lean_object * /* w */) {
    my_data * d = (my_data *) malloc(sizeof(*d));
    /* fill in d */
    return lean_io_result_mk_ok(lean_alloc_external(my_class(), d));
}
```

On the Lean side, declare an opaque type backed by a `NonemptyType`
witness. This is exactly how Lean core declares its IO handle:

```lean
private opaque MyDataPointed : NonemptyType
def MyData : Type := MyDataPointed.type
instance : Nonempty MyData := MyDataPointed.property

@[extern "my_make"] opaque MyData.make : ... → IO MyData
```

The five calls you will use most:

- `lean_register_external_class(finalize, foreach)` — once per type.
- `lean_alloc_external(cls, ptr)` — wrap a `void *`.
- `lean_get_external_data(o)` — retrieve the `void *`.
- `finalize(ptr)` — your destructor; runs when refcount hits zero.
- `foreach(ptr, f)` — used by the GC for cycle detection on nested
  `lean_object *`s; usually a no-op.

Header references: `third_party/lean4/src/include/lean/lean.h`
lines 295-310 (declarations) and 1326-1351 (`lean_alloc_external`,
`lean_get_external_data`, `lean_set_external_data`).

## ByteArray for raw bytes

`ByteArray` is the right type for "blob of bytes" — file contents,
network buffers, parsed binaries. The Lean side is a primitive; the C
side allocates with `lean_alloc_sarray(1, size, capacity)` and writes
through `lean_sarray_cptr(o)`:

```c
lean_object * arr = lean_alloc_sarray(1, len, len);
uint8_t *     buf = lean_sarray_cptr(arr);
/* fill buf... */
return lean_io_result_mk_ok(arr);
```

For reading whole files, Lean already provides `IO.FS.readBinFile`,
which is a thin wrapper over `lean_io_prim_read_bin_file` in
`third_party/lean4/src/runtime/io.cpp`. Crib that pattern if you need
a variant.

Caveat: Lean's compiler does in-place updates ("FBIP") on
`ByteArray`s when the refcount is 1. If you back a `ByteArray` with
externally managed memory (mmap'd region, etc.), the compiler may
mutate it. Prefer wrapping such memory in an external object instead.

## Borrowing foreign memory without copying

A common need: a large foreign buffer (mmap'd file, network buffer,
GPU readback) that Lean code should be able to read but that Lean
should not own or copy.

The right approach is **wrap the pointer in an external object,
expose extern accessors**. The Lean code sees an opaque handle. The
runtime reads through accessor functions that index into the foreign
buffer. No copy.

```c
typedef struct { void * addr; size_t len; } region;

static void region_finalize(void * p) {
    region * r = (region *)p;
    if (r->addr) munmap(r->addr, r->len);
    free(r);
}

extern "C" uint8_t my_region_u8(b_lean_obj_arg r_obj, size_t off) {
    region * r = (region *) lean_get_external_data(r_obj);
    /* bounds check elided */
    return ((uint8_t *) r->addr)[off];
}
```

```lean
private opaque RegionPointed : NonemptyType
def Region : Type := RegionPointed.type
instance : Nonempty Region := RegionPointed.property

@[extern "my_region_u8"]
opaque Region.u8 (r : @& Region) (off : USize) : UInt8
```

**What does not work: making foreign memory *be* a `ByteArray`.** Three
reasons:

1. *Layout.* A `lean_sarray_object` is a single allocation with
   inline bytes after its header. There is no way to point one at
   externally managed memory.
2. *FBIP.* The compiler may mutate a `ByteArray` in place when the
   refcount is 1. On `PROT_READ` memory this segfaults; on a
   file-backed `PROT_WRITE` mapping it silently corrupts the file.
3. *Allocator mismatch.* The GC frees `ByteArray` storage via Lean's
   allocator, not `munmap`/`free`.

People occasionally try to fake a `ByteArray` over external memory.
It is not worth it; the external-object pattern does the same job
without the sharp edges.

**Mental model:**
- `ByteArray` = Lean owns the bytes. Copy in if you want this.
- External object wrapping `(void *, size_t)` = foreign owns the bytes.
  Lean reads through extern accessors. The finalizer frees.

For pure-Lean reasoning over a foreign buffer, declare an opaque
abstract model and let the extern be the runtime view:

```lean
opaque Region.get : Region → Nat → Option UInt8
```

Proofs see a `Nat → Option UInt8`; compiled code reads from foreign
pages. Same dual-implementation trick the rest of the FFI layer uses.

## Build wiring with Lake

The non-obvious part: you usually need **both** a static and a
dynamic library.

- The static library (`.a`) is linked into AOT-compiled binaries
  produced by `lake build`.
- The dynamic library (`.so` / `.dylib`) is needed by the Lean
  interpreter when it encounters an `@[extern]` call during
  `#eval` or in editor sessions. Without it: missing-symbol errors.

The `lakefile.lean` (still the most expressive form) for SampCert
demonstrates the full pattern:
`third_party/SampCert/lakefile.lean:14-46`. Three targets:

```lean
target ffi.o (pkg : NPackage __name__) : FilePath := do
  let oFile := pkg.buildDir / "ffi.o"
  let srcFile ← inputFile (pkg.dir / "ffi.cpp") false
  let lean ← getLeanInstall
  buildO oFile srcFile
    (weakArgs := #[s!"-I{lean.includeDir}"])
    (traceArgs := #["-fPIC"])
    (compiler := "g++")

target libleanffi (pkg : NPackage __name__) : FilePath := ...    -- static
target libleanffidyn (pkg : NPackage __name__) : Dynlib := ...   -- shared

@[default_target]
lean_lib MyLib where
  extraDepTargets := #[`libleanffi, `libleanffidyn]

lean_exe my_exe where
  root := `Main
  extraDepTargets := #[`libleanffi]
  moreLinkArgs := #["-L.lake/build/lib", "-lleanffi"]
```

Compile flags worth carrying:
- `-I {leanIncludeDir}` for `<lean/lean.h>`.
- `-fPIC` for the dynlib.
- `-Wl,-rpath,{leanLibDir}` so the dynlib finds `libleanrt` at run
  time.

Lake's native-target API has shifted between Lean versions; the
pattern above tracks current Lake (4.28+). Lakefile.toml supports the
same idea but is less expressive for custom targets — for nontrivial
FFI, prefer `lakefile.lean`.

## Calling Lean from C (reverse FFI)

Mostly the inverse: `@[export name]` gives a Lean function an
unmangled symbol; the C side calls it after initializing the Lean
runtime. The required dance is:

```c
lean_initialize_runtime_module();
lean_object * res = initialize_MyModule(/*builtin=*/1, lean_io_mk_world());
if (lean_io_result_is_ok(res)) lean_dec_ref(res);
else { lean_io_result_show_error(res); lean_dec(res); return 1; }
lean_io_mark_end_initialization();
/* now safe to call exported Lean symbols */
```

If you use `IO.Process` features, also call `lean_setup_args(argc, argv)`
*before* `lean_initialize_runtime_module`. Module initializers are
idempotent but **not** thread-safe; threads spawned outside Lean must
call `lean_initialize_thread()` and `lean_finalize_thread()`.

The canonical worked example lives in
`third_party/lean4/tests/lake/examples/ffi/` (and its reverse-FFI
sibling).

## Pitfalls

These are the ones people hit repeatedly:

- **Same-module interpreter limitation.** You cannot `#eval` an
  `@[extern]` declaration in the file that declares it. The
  interpreter needs the compiled module loaded as a dynlib. Move the
  declaration to a separate module and import it.
- **Static lib without dynlib.** `lake build` works, then `#eval`
  blows up with a missing symbol. Always build both.
- **Owned/borrowed mismatch.** Annotate with `@&` exactly when the C
  body does not call `lean_dec` on that argument. Run leak/asan tests
  early.
- **Forgetting `lean_inc` before `lean_apply_n`.** Apply consumes its
  inputs.
- **External class registered twice.** `lean_register_external_class`
  returns a fresh class each call. Cache it in a `static` variable.
- **`lean_string_cstr` lifetime.** The pointer is valid only while the
  source `lean_object *` is alive. Copy if you need to retain.
- **`@[extern]` on a function the kernel needs to reduce.** The kernel
  only sees the Lean body, not the C symbol. If you need `decide` or
  `rfl` to compute through the function, do not extern it.
- **Symbol name collisions.** Extern symbols share a flat C namespace.
  Use a project-specific prefix (`yourproj_foo`).
- **`struct` by value across the boundary.** Not supported. Pass by
  pointer wrapped in an external object, or marshal fields.
- **Compiler in-place mutation of `ByteArray`s.** If you back a
  `ByteArray` with non-Lean-managed memory, FBIP may corrupt it. Use
  external objects for foreign-owned memory.

## Reference projects

Read in roughly this order, depending on what you are doing:

**Tutorials / minimal templates**
- `tests/lake/examples/ffi` and `examples/reverse_ffi` in
  `third_party/lean4/` — the official minimal examples.
- The Lean reference manual section on FFI:
  https://lean-lang.org/doc/reference/latest/Run-Time-Code/Foreign-Function-Interface/
- "Understanding Lean's Foreign Function Interface" gist by ydewit:
  https://gist.github.com/ydewit/7ab62be1bd0fea5bd53b48d23914dd6b
- `DSLstandard/Lean4-FFI-Programming-Tutorial-GLFW` — extended walk
  through binding GLFW, including opaque pointers and callbacks.

**In-tree examples**
- `third_party/lean4/src/Init/System/IO.lean` paired with
  `src/runtime/io.cpp` — the canonical file/handle/process bindings.
  Treat as ground truth for `open`, `read`, `write`, file system.
- `third_party/lean4/src/include/lean/lean.h` — the API reference.
  Worth one careful end-to-end skim.
- `third_party/SampCert` — small, end-to-end FFI project (~70 lines
  of C++). Demonstrates the dual-implementation pattern: Lean body is
  a mathematical spec, C body is the runtime sampler.

**Toolkits and libraries**
- `tydeu/lean4-alloy` — inline C inside `.lean` files via Lake module
  facets. Lighter ceremony for small shims.
- `alexf91/lean4-ctypes` — Python-`ctypes`-style dynamic loading.
- `KislyjKisel/lean4-raylib` — heaviest open-source binding to a real
  C library. Struct marshalling, callbacks, opaque handles.
- `xubaiw/Socket.lean` — small, readable POSIX socket bindings via
  external objects.

**Industrial uses**
- AWS Cedar (`third_party/cedar-spec`) — Lean as a verified spec, with
  the production Rust implementation cross-checked via differential
  testing. Uses FFI lightly, mostly through the export side.
- AWS LNSym (`third_party/LNSym`) — symbolic Arm machine-code
  reasoning. Uses `@[extern]` for performance-critical primitives.

## Sources

- Lean reference manual, FFI section:
  https://lean-lang.org/doc/reference/latest/Run-Time-Code/Foreign-Function-Interface/
- Lean reference manual, Reference Counting section:
  https://lean-lang.org/doc/reference/latest/Run-Time-Code/Reference-Counting/
- Lean source: `third_party/lean4/src/include/lean/lean.h`,
  `src/Init/System/IO.lean`, `src/runtime/io.cpp`,
  `tests/lake/examples/ffi/`.
- `tydeu/lean4-alloy` — https://github.com/tydeu/lean4-alloy
- `alexf91/lean4-ctypes` — https://github.com/alexf91/lean4-ctypes
- `DSLstandard/Lean4-FFI-Programming-Tutorial-GLFW` —
  https://github.com/DSLstandard/Lean4-FFI-Programming-Tutorial-GLFW
- `ydewit` FFI gist —
  https://gist.github.com/ydewit/7ab62be1bd0fea5bd53b48d23914dd6b
- SampCert (`third_party/SampCert`) — https://github.com/leanprover/SampCert
