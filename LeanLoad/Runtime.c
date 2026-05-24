/* LeanLoad runtime shims — single trust seam between Lean and the
 * kernel. Counterpart to `LeanLoad/Runtime/IO.lean`.
 *
 * Two topic groups:
 *   1. IO ops — file ops + memory ops. Lean's `Runtime.File` carries a
 *      transparent `uint32_t` fd plus the regular-file size captured by
 *      `fstat(2)`. Lifetime is process-bounded (we never close; the
 *      loaded program inherits the fd table when `exec_run` switches
 *      stack). All addresses cross the boundary as `uint64_t`.
 *   2. Control transfer — `leanload_exec_run` builds the
 *      kernel-`exec`-style stack and switches SP. Doesn't return.
 *
 * Bounds proofs live entirely on the Lean side; externs trust
 * addresses computed by the safe `Layout.Region.*` accessors.
 *
 * Audited by inspection (~150 lines), not proven.
 */

#include <lean/lean.h>
#include <errno.h>
#include <fcntl.h>
#include <limits.h>
#include <signal.h>
#include <stddef.h>
#include <stdint.h>
#include <stdlib.h>
#include <string.h>
#include <sys/auxv.h>
#include <sys/mman.h>
#include <sys/stat.h>
#include <unistd.h>

/* Wrap a C string as a `lean_io_result_mk_error`. */
static inline lean_object * leanload_io_err(const char * msg) {
    return lean_io_result_mk_error(
        lean_mk_io_user_error(lean_mk_string(msg)));
}

/* ============================================================
 * File operations
 * ============================================================ */

/* Try `prefix[0..prefix_len)/soname` — open RDONLY|CLOEXEC. Returns
 * fd on success, -1 otherwise. Skips empty prefixes. `buf` is a
 * scratch area sized for the concatenation. */
static int leanload_try_open_concat(const char *prefix, size_t prefix_len,
                                    const char *soname, size_t soname_len,
                                    char *buf, size_t buf_size) {
    if (prefix_len == 0) return -1;
    /* prefix + '/' + soname + '\0' */
    if (prefix_len + 1 + soname_len + 1 > buf_size) return -1;
    memcpy(buf, prefix, prefix_len);
    buf[prefix_len] = '/';
    memcpy(buf + prefix_len + 1, soname, soname_len + 1);  /* include NUL */
    return open(buf, O_RDONLY | O_CLOEXEC);
}

/* For each colon-separated entry in `list`, try opening `<entry>/<soname>`.
 * Returns fd on first success, or -1 if no entry succeeded. */
static int leanload_search_path_list(const char *list,
                                     const char *soname, size_t soname_len,
                                     char *buf, size_t buf_size) {
    const char *p = list;
    while (*p) {
        const char *colon = strchr(p, ':');
        size_t len = colon ? (size_t)(colon - p) : strlen(p);
        int fd = leanload_try_open_concat(p, len, soname, soname_len,
                                           buf, buf_size);
        if (fd >= 0) return fd;
        if (!colon) break;
        p = colon + 1;
    }
    return -1;
}

/* Open the file backing `soname`. Search rules (mirrors gabi 08
 * § Shared Object Dependencies):
 *
 *   1. If `soname` contains '/', open as a literal path (no search).
 *   2. Else for each ':'-separated entry in `LD_LIBRARY_PATH`,
 *      try `open("<entry>/<soname>", ...)`. First success wins.
 *   3. Else for each ':'-separated entry in `runpath` (if some),
 *      same. (DT_RUNPATH; DT_RPATH is deprecated, not honoured.)
 *   4. Else return `none`.
 *
 * Returns `IO (Option UInt32)` — the open fd, or `none` if no
 * candidate existed. Lean derives the canonical dedup key from
 * `DT_SONAME` (read after parse) — no path needed back from C.
 * Open errors propagate as `none`; the BFS surfaces them with the
 * full WorkItem context (runpath, soname) attached. */
LEAN_EXPORT lean_object * leanload_open_by_name(
        b_lean_obj_arg soname_obj,
        b_lean_obj_arg runpath_opt,
        lean_object * /* w */) {
    const char * soname = lean_string_cstr(soname_obj);
    size_t soname_len = strlen(soname);
    int fd = -1;

    if (strchr(soname, '/') != NULL) {
        /* Case 1: literal path. */
        fd = open(soname, O_RDONLY | O_CLOEXEC);
    } else {
        char buf[PATH_MAX];
        /* Case 2: LD_LIBRARY_PATH. */
        const char * env = getenv("LD_LIBRARY_PATH");
        if (env != NULL) {
            fd = leanload_search_path_list(env, soname, soname_len,
                                            buf, sizeof(buf));
        }
        /* Case 3: runpath. `runpath_opt` is `Option String` —
         * tag 0 = none, tag 1 = some (with the string at field 0). */
        if (fd < 0 && lean_obj_tag(runpath_opt) == 1) {
            lean_object * rp_str = lean_ctor_get(runpath_opt, 0);
            const char * runpath = lean_string_cstr(rp_str);
            fd = leanload_search_path_list(runpath, soname, soname_len,
                                            buf, sizeof(buf));
        }
    }

    if (fd < 0) {
        /* Option.none = ctor 0, no fields = lean_box(0). */
        return lean_io_result_mk_ok(lean_box(0));
    }
    /* Option.some UInt32 = ctor 1, one field. */
    lean_object * some = lean_alloc_ctor(1, 1, 0);
    lean_ctor_set(some, 0, lean_box_uint32((uint32_t)fd));
    return lean_io_result_mk_ok(some);
}

/* Return the observed regular-file size for an open fd. */
LEAN_EXPORT lean_object * leanload_file_size(uint32_t fd, lean_object * /* w */) {
    struct stat st;
    if (fstat((int)fd, &st) != 0) {
        return leanload_io_err(strerror(errno));
    }
    if (!S_ISREG(st.st_mode) || st.st_size < 0) {
        return leanload_io_err("open file is not a regular file with a nonnegative size");
    }
    return lean_io_result_mk_ok(lean_box_uint64((uint64_t)st.st_size));
}

/* `pread(2)` exactly `len` bytes at `offset` into a fresh ByteArray.
 * Errors on partial reads — for regular files (the only kind we open)
 * `pread` either delivers all requested bytes or fails. */
LEAN_EXPORT lean_object * leanload_pread(uint32_t fd,
                                         uint64_t offset,
                                         uint64_t len,
                                         lean_object * /* w */) {
    lean_object * arr = lean_alloc_sarray(1, (size_t)len, (size_t)len);
    ssize_t n = pread((int)fd, lean_sarray_cptr(arr), (size_t)len, (off_t)offset);
    if (n != (ssize_t)len) {
        lean_dec_ref(arr);
        return leanload_io_err(n < 0 ? strerror(errno) : "short read");
    }
    return lean_io_result_mk_ok(arr);
}

/* ============================================================
 * Memory operations
 * ============================================================ */

/* File-backed `MAP_PRIVATE | MAP_FIXED` overlay at `vaddr`. */
LEAN_EXPORT lean_object * leanload_mmap_file(uint32_t fd,
                                             uint64_t vaddr,
                                             uint64_t len,
                                             uint32_t prot,
                                             uint64_t offset,
                                             lean_object * /* w */) {
    void * p = mmap((void *)(uintptr_t)vaddr, (size_t)len, (int)prot,
                    MAP_PRIVATE | MAP_FIXED, (int)fd, (off_t)offset);
    if (p == MAP_FAILED) {
        return leanload_io_err(strerror(errno));
    }
    return lean_io_result_mk_ok(lean_box(0));
}

/* Kernel-picked anon mapping, `len` bytes. Kernel returns the
 * chosen base; caller threads it into pure planning (per-load
 * reservation) or into `exec_run` (loaded program's stack). */
LEAN_EXPORT lean_object * leanload_mmap_anon(uint64_t len,
                                             lean_object * /* w */) {
    void * p = mmap(NULL, (size_t)len,
                    PROT_READ | PROT_WRITE,
                    MAP_PRIVATE | MAP_ANONYMOUS, -1, 0);
    if (p == MAP_FAILED) {
        return leanload_io_err(strerror(errno));
    }
    return lean_io_result_mk_ok(lean_box_uint64((uint64_t)(uintptr_t)p));
}

/* mprotect over `[addr, addr+len)`. */
LEAN_EXPORT lean_object * leanload_mprotect(uint64_t addr,
                                            uint64_t len,
                                            uint32_t prot,
                                            lean_object * /* w */) {
    void * start = (void *)(uintptr_t)addr;
    if (mprotect(start, (size_t)len, (int)prot) != 0) {
        return leanload_io_err(strerror(errno));
    }
    if (prot & PROT_EXEC) {
        __builtin___clear_cache((char *)start, (char *)start + len);
    }
    return lean_io_result_mk_ok(lean_box(0));
}

/* Store the low `size` (4 or 8) little-endian bytes of `value` at
 * `addr`. The relocation formula computes a uint64; we truncate to
 * `size` bytes by memcpy'ing only the low ones. */
LEAN_EXPORT lean_object * leanload_store(uint64_t addr,
                                         uint8_t size,
                                         uint64_t value,
                                         lean_object * /* w */) {
    memcpy((void *)(uintptr_t)addr, &value, (size_t)size);
    return lean_io_result_mk_ok(lean_box(0));
}

/* Zero `len` bytes starting at `addr`. */
LEAN_EXPORT lean_object * leanload_zero(uint64_t addr,
                                        uint64_t len,
                                        lean_object * /* w */) {
    memset((void *)(uintptr_t)addr, 0, (size_t)len);
    return lean_io_result_mk_ok(lean_box(0));
}

/* ============================================================
 * Control transfer
 * ============================================================
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
 * `getauxval`. The host-process values are valid for the loaded
 * binary because we load into our own process. musl's
 * `__libc_start_main` uses many of these for runtime feature
 * detection, identity, and the vDSO; without them it crashes.
 *
 * AArch64 and x86-64 supported. */

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
 * gabi 08 documents `void (*)(int, char**, char**)` but freestanding
 * ctors ignore those, and the no-arg form avoids any chance of a
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
    uint64_t stack_va,
    uint64_t stack_len,
    b_lean_obj_arg argv0_str,
    lean_object * /* world */) {

    if (entry == 0) return leanload_io_err("exec: null entry");
    if (!stack_va || stack_len < 4096) {
        return leanload_io_err("exec: stack region missing or too small");
    }

    const char * argv0 = lean_string_cstr(argv0_str);
    size_t argv0_len = strlen(argv0) + 1;

    /* Strings near the top of the region. */
    char * top = (char *)(uintptr_t)stack_va + stack_len;
    char * argv0_dst = top - argv0_len;
    memcpy(argv0_dst, argv0, argv0_len);

    /* AT_RANDOM points at 16 bytes of entropy. Always copy from the
     * host's `getauxval(AT_RANDOM)`. */
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
     * `__libc_start_main` needs these for feature detection,
     * identity, and the vDSO. */
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
