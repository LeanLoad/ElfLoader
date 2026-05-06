/* Hand control of the process to a loaded image.
 *
 * Builds the stack the kernel hands a freshly-`exec`'d process,
 * switches the stack pointer onto it, and `br`s to the binary's
 * entry point. Does not return: the loaded program terminates the
 * process via the `exit` syscall.
 *
 * Stack layout (low → high; SP points at `argc`):
 *
 *   argc
 *   argv[0]      → string
 *   argv[1] = NULL
 *   envp[0]    = NULL
 *   auxv pairs (a_type, a_val), terminated by AT_NULL
 *   ...padding...
 *   16 random bytes (referenced by AT_RANDOM)
 *   "argv0\0"
 *
 * The auxv we forward includes both binary-specific values
 * (AT_PHDR/PHENT/PHNUM/ENTRY) and host-process values pulled via
 * `getauxval` (AT_HWCAP/HWCAP2/CLKTCK/UID/EUID/GID/EGID/SECURE/SYSINFO_EHDR).
 * The host-process values are valid for the loaded binary because we
 * load into our own process. musl's `__libc_start_main` uses many of
 * these for runtime feature detection, identity, and the vDSO; without
 * them it crashes or hangs.
 *
 * AArch64 and x86-64 supported.
 */

#include "runtime.h"
#include <signal.h>
#include <stdint.h>
#include <string.h>
#include <sys/auxv.h>
#include <unistd.h>

#define AT_NULL         0
#define AT_PHDR         3
#define AT_PHENT        4
#define AT_PHNUM        5
#define AT_PAGESZ       6
#define AT_BASE         7
#define AT_FLAGS        8
#define AT_ENTRY        9
#define AT_UID         11
#define AT_EUID        12
#define AT_GID         13
#define AT_EGID        14
#define AT_HWCAP       16
#define AT_CLKTCK      17
#define AT_SECURE      23
#define AT_RANDOM      25
#define AT_HWCAP2      26
#define AT_EXECFN      31
#define AT_SYSINFO_EHDR 33

static long * push_auxv(long * sp, long tag, long val) {
    *sp++ = tag;
    *sp++ = val;
    return sp;
}

/* Call a single init/fini function as `extern "C" fn()` — no args.
 * Mirrors VeriLoad (`runtime.rs:294-296`). gabi 08 documents
 * `void (*)(int, char**, char**)` but freestanding ctors ignore
 * those, and matching VeriLoad's signature avoids any chance of a
 * ctor mis-reading register-passed args. */
LEAN_EXPORT lean_object * leanload_exec_call_ctor(uint64_t addr,
                                                  lean_object * /* w */) {
    if (addr == 0) return leanload_io_err("call_ctor: null address");
    typedef void (*ctor_t)(void);
    ((ctor_t)(uintptr_t)addr)();
    return lean_io_result_mk_ok(lean_box(0));
}

LEAN_EXPORT lean_object * leanload_exec_run(
    uint64_t entry,
    uint64_t phdr_va,
    uint64_t phent,
    uint64_t phnum,
    uint64_t base_va,
    b_lean_obj_arg stack_region,
    b_lean_obj_arg argv0_str,
    lean_object * /* world */) {

    if (entry == 0) return leanload_io_err("exec: null entry");

    leanload_region * sr = (leanload_region *)lean_get_external_data(stack_region);
    if (!sr->addr || sr->length < 4096) {
        return leanload_io_err("exec: stack region missing or too small");
    }

    const char * argv0 = lean_string_cstr(argv0_str);
    size_t argv0_len = strlen(argv0) + 1;

    /* Strings near the top of the region. */
    char * top = (char *)sr->addr + sr->length;
    char * argv0_dst = top - argv0_len;
    memcpy(argv0_dst, argv0, argv0_len);

    /* AT_RANDOM points at 16 bytes of entropy. Always copy from the
     * host's `getauxval(AT_RANDOM)` (matches VeriLoad
     * `runtime.rs:188-193`). The host always has these — kernel
     * provides them at process start. */
    char * random_dst = (char *)((uintptr_t)(argv0_dst - 16) & ~(uintptr_t)15);
    memcpy(random_dst, (const char *)getauxval(AT_RANDOM), 16);

    /* Reserve space for argc + argv + envp + ~20 auxv pairs. */
    uintptr_t after_data = (uintptr_t)random_dst & ~(uintptr_t)15;
    long * sp = (long *)(after_data - 16 * 32);
    sp = (long *)((uintptr_t)sp & ~(uintptr_t)15);

    long * w = sp;
    *w++ = 1;                   /* argc                  */
    *w++ = (long)argv0_dst;     /* argv[0]               */
    *w++ = 0;                   /* argv[1] = NULL        */
    *w++ = 0;                   /* envp[0] = NULL        */

    /* Binary-specific auxv. */
    if (phdr_va) {
        w = push_auxv(w, AT_PHDR,  (long)phdr_va);
        w = push_auxv(w, AT_PHENT, (long)phent);
        w = push_auxv(w, AT_PHNUM, (long)phnum);
    }
    w = push_auxv(w, AT_PAGESZ, 4096);
    w = push_auxv(w, AT_BASE,   (long)base_va);
    w = push_auxv(w, AT_FLAGS,  0);
    w = push_auxv(w, AT_ENTRY,  (long)entry);
    w = push_auxv(w, AT_RANDOM, (long)random_dst);
    w = push_auxv(w, AT_EXECFN, (long)argv0_dst);
    w = push_auxv(w, AT_SECURE, 0);

    /* Host-process auxv (forwarded via `getauxval`). musl's
     * `__libc_start_main` needs these for feature detection, identity,
     * and the vDSO. */
    w = push_auxv(w, AT_UID,    (long)getauxval(AT_UID));
    w = push_auxv(w, AT_EUID,   (long)getauxval(AT_EUID));
    w = push_auxv(w, AT_GID,    (long)getauxval(AT_GID));
    w = push_auxv(w, AT_EGID,   (long)getauxval(AT_EGID));
    long hwcap  = (long)getauxval(AT_HWCAP);   if (hwcap)  w = push_auxv(w, AT_HWCAP,  hwcap);
    long hwcap2 = (long)getauxval(AT_HWCAP2);  if (hwcap2) w = push_auxv(w, AT_HWCAP2, hwcap2);
    long clktck = (long)getauxval(AT_CLKTCK);  if (clktck) w = push_auxv(w, AT_CLKTCK, clktck);
    long sysinfo_ehdr = (long)getauxval(AT_SYSINFO_EHDR);
    if (sysinfo_ehdr) w = push_auxv(w, AT_SYSINFO_EHDR, sysinfo_ehdr);

    w = push_auxv(w, AT_NULL, 0);

    /* Reset signal handlers to default before transferring control,
     * so the loaded binary's faults kill cleanly instead of waking
     * Lean's segv_handler (which calls `pthread_getattr_np` and
     * deadlocks against libuv's pthread lock when leanload's own
     * threads are still alive). */
    {
        struct sigaction sa;
        memset(&sa, 0, sizeof(sa));
        sa.sa_handler = SIG_DFL;
        sigemptyset(&sa.sa_mask);
        sa.sa_flags = 0;
        sigaction(SIGSEGV, &sa, NULL);
        sigaction(SIGBUS,  &sa, NULL);
        sigaction(SIGILL,  &sa, NULL);
        sigaction(SIGFPE,  &sa, NULL);
        sigaction(SIGABRT, &sa, NULL);
        sigaction(SIGPIPE, &sa, NULL);
    }
    sigset_t empty;
    sigemptyset(&empty);
    sigprocmask(SIG_SETMASK, &empty, NULL);

#if defined(__aarch64__)
    asm volatile(
        "mov sp, %0\n"
        "br  %1\n"
        :
        : "r"(sp), "r"(entry)
        : "memory");
#elif defined(__x86_64__)
    /* SysV x86-64 § Initial Stack and Register State:
     *   - RSP must be 16-byte aligned and point at argc
     *   - RBP zeroed marks the deepest frame
     *   - RDX holds an atexit() function pointer; NULL means "none"
     * The kernel zeroes other registers; for our purposes the
     * inputs alone suffice — the loaded `_start` saves whatever it
     * needs from the stack. */
    asm volatile(
        "movq %0, %%rsp\n"
        "xorq %%rbp, %%rbp\n"
        "xorq %%rdx, %%rdx\n"
        "jmpq *%1\n"
        :
        : "r"(sp), "r"(entry)
        : "memory");
#else
# error "leanload_exec_run: unsupported architecture (need __aarch64__ or __x86_64__)"
#endif
    __builtin_unreachable();
}
