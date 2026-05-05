# Kernel-Style Exec

How LeanLoad transfers control from itself to a loaded ELF image.

## What the kernel does on `execve`

When a normal program runs, the kernel:

1. Maps the binary's `PT_LOAD` segments at their `p_vaddr`.
2. `mprotect`s each segment to its `p_flags` permissions.
3. If `PT_INTERP` is set, loads the dynamic linker too.
4. Allocates a fresh user stack (~8 MiB by default).
5. Builds the **kernel exec stack** on it (layout below).
6. Sets `SP` to the base of that layout and jumps to `e_entry`.

LeanLoad's `Load.load` mirrors steps 1-2 in pure Lean (`Link.Layout`)
plus an FFI `mmap`, then steps 4-6 in `runtime/exec.c`.

## Stack layout

The kernel hands `_start` a stack laid out like this (low → high):

```
sp →  argc                          long
      argv[0]            → string
      argv[1]
      ...
      argv[argc-1]
      argv[argc]   = NULL
      envp[0]            → string
      envp[1]
      ...
      envp[k-1]
      envp[k]      = NULL
      auxv[0].a_type     → e.g. AT_RANDOM
      auxv[0].a_val
      ...
      auxv[n].a_type = AT_NULL
      auxv[n].a_val  = 0
      ───── argv / envp / auxv strings live above this point ─────
      "argv0\0envp0\0..."
```

`_start` (the binary's entry) reads `argc` from `*sp`, computes argv as
`sp+1`, then jumps into `_start_c` (or its libc equivalent) which walks
envp until NULL to find auxv, runs init constructors, calls `main`, and
on return invokes `exit(rc)`.

## What `runtime/exec.c` builds

For Phase 2 we keep this minimal: one argv entry (the binary path), no
environment, auxv contains only `AT_NULL`. That's enough for nolibc's
`_start_c` and any static program that doesn't introspect its
environment.

```
sp →  argc            = 1
      argv[0]         → "<path>"
      argv[1]         = NULL
      envp[0]         = NULL
      auxv[0].tag     = AT_NULL (0)
      auxv[0].val     = 0
      ...padding to 16-byte alignment...
      "<path>\0"
```

The string is laid out near the top of the caller-supplied stack
region; SP is rounded down to a 16-byte boundary (AArch64 ABI).

## The trampoline

After the layout is in place, two AArch64 instructions do the handover:

```asm
mov sp, x0    ; switch SP to our prepared stack
br  x1        ; jump to entry (no return address pushed)
```

`br` (not `bl`) is deliberate: there is no return. Once we transfer
control, leanload's process is the loaded program. It terminates the
process via the `exit` syscall.

## Lifetime of the image regions

Across the call to `Exec.run`, the image regions must remain mapped.
Lean's optimizer would normally drop the `Array Region` after the call
(since the call is the last use), running each region's finalizer and
`munmap`ing the code we are about to execute.

Two countermeasures:

- `Exec.run` declares `keepAlive : @& Array Region` as a borrowed
  parameter. Lean's compiler sees the array is borrowed across the
  call and keeps it live until the call site.
- `Exec.run` is `IO Unit` but the C body never returns. After the
  call there is no Lean code to drop the array; the references stay
  pinned for the life of the process.

The `Handle` type (in `LeanLoad.Load`) bundles the regions plus the
entry address. As long as the `Handle` is reachable, its regions stay
mapped.

## Multi-threaded host vs. `__NR_exit`

A subtle gotcha when using kernel-style exec **inside** a multi-threaded
process: nolibc's (and most freestanding libc's) `exit()` uses
`__NR_exit` (93 on AArch64), which exits only the *calling thread*. A
real kernel `execve` replaces the entire process image, so there's
nothing else to leave behind. Leanload, by contrast, runs Lean's
runtime threads (GC, task scheduler, etc.) alongside the loaded
binary — so when the loaded binary calls its `exit()`, only the
calling thread dies and the process hangs forever.

Workaround in the fixture: bypass `exit()` and call `__NR_exit_group`
(94) directly via `my_syscall1`. That kills every thread and the
process actually terminates.

A more invasive fix on the loader side would be to tear down Lean's
threads before transferring control. We don't need that yet; the
fixture-side workaround is one line.

## What's deferred

- **`AT_RANDOM`, `AT_PAGESZ`, `AT_PHDR`, ...**: real auxv entries.
  Required for stack canaries (musl's `__stack_chk_init`), TLS setup,
  and `dl_iterate_phdr`.
- **Real environment**: reading argv/envp from leanload's caller and
  forwarding them.
- **Multiple argv entries**: pass-through of leanload's command line.
- **x86-64 trampoline**: currently AArch64 only.
- **Stack guard pages**: a real exec gives the process a guard page at
  the bottom of the stack region.
- **Signal handlers / sigaltstack**: not relevant for static fixtures
  but real programs depend on them.

These land in Phase 3+ as needed.

## Files

- `runtime/exec.h`, `runtime/exec.c` — stack builder + trampoline.
- `runtime/region.{h,c}`, `runtime/common.h` — shared region machinery.
- `LeanLoad/FFI/Exec.lean` — extern declaration.
- `LeanLoad/Load.lean` — orchestration (`load`).
- `examples/static.c` — fixture using nolibc's `_start_c` / `main`.
