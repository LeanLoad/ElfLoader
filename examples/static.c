// Static fixture for LeanLoad Phase 2.
//
// Built with nolibc's `_start` / `_start_c` CRT. Loaded by leanload's
// kernel-style exec mode, which builds the kernel-style stack
// (argc / argv / envp / auxv) before transferring control.
//
// Build:
//   cc -static -no-pie -nostdlib -I<nolibc> static.c -o static
//
// Output: prints `hello from leanload`, terminates with status 42.

#include "sys.h"

int main(int argc, char **argv) {
    (void)argc; (void)argv;
    static const char msg[] = "hello from leanload\n";
    sys_write(1, msg, sizeof(msg) - 1);

    // Terminate the whole process. nolibc's `exit()` uses `__NR_exit`
    // (93), which only kills the calling thread — fine after a real
    // `execve` that replaces the process image, but leanload loads
    // us into its existing multi-threaded process where the Lean
    // runtime threads would survive. `__NR_exit_group` (94) kills
    // every thread.
    my_syscall1(__NR_exit_group, 42);
    __builtin_unreachable();
}
