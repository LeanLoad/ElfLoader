/-
FFI: hand control of the process to a loaded ELF image.

`run` builds the stack a kernel-`exec`'d process would see and jumps
to entry. It does not return — leanload's process becomes the loaded
program, which terminates the process itself.
-/

import LeanLoad.FFI.Region

namespace LeanLoad.FFI.Exec

/-- Hand control to a loaded image.

    Builds the kernel-style exec stack on `stack` (argc, argv[],
    envp[], auxv[]), switches SP to it, and jumps to `entry`.
    **Does not return** — the loaded program owns the process.

    Auxv entries supplied:
    - `AT_PHDR`/`AT_PHENT`/`AT_PHNUM` if `phdrVa ≠ 0` (real glibc/musl
      need these for `dl_iterate_phdr` and stack-protector setup).
    - `AT_PAGESZ = 4096`.
    - `AT_BASE` if `baseVa ≠ 0` (the dynamic linker base, normally 0
      since we are the loader).
    - `AT_ENTRY = entry`.
    - `AT_RANDOM` pointing at 16 bytes on the stack (deterministic for
      now; satisfies stack canary readers).

    Image regions must be `Region.pin`-ed before calling this; the
    optimizer may otherwise `munmap` the loaded code before transfer.

    AArch64 only at present. -/
@[extern "leanload_exec_run"]
opaque run
  (entry  : UInt64)
  (phdrVa : UInt64)
  (phent  : UInt64)
  (phnum  : UInt64)
  (baseVa : UInt64)
  (stack  : @& LeanLoad.FFI.Region.Region)
  (argv0  : @& String) : IO Unit

/-- Call a constructor / destructor function by its absolute address.
    Signature per gabi 08: `void (*)(int argc, char **argv, char **envp)`.
    We pass `(0, NULL, NULL)`; freestanding ctors typically ignore them. -/
@[extern "leanload_exec_call_ctor"]
opaque callCtor (addr : UInt64) : IO Unit

end LeanLoad.FFI.Exec
