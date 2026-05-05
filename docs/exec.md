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

LeanLoad mirrors steps 1-2 in pure Lean (`Plan.Layout`) plus FFI
`mmap` (`Map.lean`), then steps 4-6 in `runtime/exec.c`.

## Stack layout

The kernel hands `_start` a stack laid out like this (low → high):

```
sp →  argc                          long
      argv[0]            → string
      argv[1]
      ...
      argv[argc]   = NULL
      envp[0]            → string
      ...
      envp[k]      = NULL
      auxv[0].a_type     → e.g. AT_RANDOM
      auxv[0].a_val
      ...
      auxv[n].a_type = AT_NULL
      auxv[n].a_val  = 0
      ───── argv / envp / auxv strings live above this point ─────
      "argv0\0..."
```

`_start` reads `argc` from `*sp`, computes argv as `sp+1`, walks envp
to find auxv, runs init constructors, calls `main`, and on return
invokes `exit(rc)`.

## Auxv entries we supply

`runtime/exec.c::leanload_exec_run` populates the auxv with:

- **Binary-specific** — pulled from the parsed ELF and the chosen
  base address: `AT_PHDR`, `AT_PHENT`, `AT_PHNUM`, `AT_PAGESZ`
  (4096), `AT_BASE`, `AT_FLAGS`, `AT_ENTRY`, `AT_EXECFN`.
- **Random** — `AT_RANDOM` points at 16 bytes copied from the host's
  own `getauxval(AT_RANDOM)`. musl's stack-canary init reads this.
- **Host-process forward** — `AT_UID`, `AT_EUID`, `AT_GID`, `AT_EGID`,
  `AT_HWCAP`, `AT_HWCAP2`, `AT_CLKTCK`, `AT_SECURE`, `AT_SYSINFO_EHDR`.
  Pulled via `getauxval` because we run inside leanload's own process
  and these are valid for the loaded binary too.

Without these, musl's `__libc_start_main` crashes or hangs in
feature-detection / identity / vDSO code paths.

SP is rounded down to a 16-byte boundary — required by both the
AArch64 ABI and the SysV x86-64 ABI § Initial Stack and Register
State.

## The trampoline

After the layout is in place, a few instructions do the handover.
On AArch64:

```asm
mov sp, x0    ; switch SP to our prepared stack
br  x1        ; jump to entry (no return address pushed)
```

On x86-64 (per SysV § Initial Stack and Register State):

```asm
movq %rax, %rsp   ; switch SP to our prepared stack
xorq %rbp, %rbp   ; mark deepest frame
xorq %rdx, %rdx   ; no atexit handler to register
jmpq *%rbx        ; jump to entry (no return address pushed)
```

`br` / `jmp` (not `bl` / `call`) is deliberate: there is no return.
Once we transfer control, leanload's process *is* the loaded
program. It terminates the process via `exit_group(2)`.

## Signal-handler reset

Just before transfer of control, `runtime/exec.c` resets `SIGSEGV`,
`SIGBUS`, `SIGILL`, `SIGFPE`, `SIGABRT`, `SIGPIPE` to `SIG_DFL` and
clears the signal mask. Without this, the loaded binary's faults
would wake Lean's `segv_handler`, which calls `pthread_getattr_np`
and deadlocks against libuv's pthread lock (Lean's runtime threads
are still alive).

## Multi-threaded host vs. `__NR_exit`

A subtle gotcha when using kernel-style exec **inside** a
multi-threaded process: nolibc's `exit()` (and any freestanding libc
that uses it) issues `__NR_exit` (93 on AArch64), which exits only
the *calling thread*. A real kernel `execve` replaces the entire
process image, so there's nothing else to leave behind. Leanload, by
contrast, runs Lean's runtime threads (GC, task scheduler, …)
alongside the loaded binary — so when the loaded binary calls its
`exit()`, only the calling thread dies and the process hangs.

Workaround in the static fixture (`examples/static.c`): bypass
`exit()` and call `__NR_exit_group` (94) directly via `my_syscall1`.
musl's `_exit` already does the right thing.

## Files

- `runtime/exec.{h,c}` — stack builder + trampoline.
- `runtime/region.{h,c}`, `runtime/common.h` — shared region machinery.
- `LeanLoad/Exec.lean` — `@[extern]` declarations + Lean orchestration.
- `LeanLoad/Main.lean` — top-level `load` function.
- `examples/static.c` — minimal nolibc fixture.
