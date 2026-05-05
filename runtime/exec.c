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
 * AArch64 only at present.
 */

#include "exec.h"
#include "region.h"
#include "common.h"
#include <stdint.h>
#include <string.h>

/* Auxv tag numbers (subset; <linux/auxvec.h>). */
#define AT_NULL    0
#define AT_PHDR    3
#define AT_PHENT   4
#define AT_PHNUM   5
#define AT_PAGESZ  6
#define AT_BASE    7
#define AT_ENTRY   9
#define AT_RANDOM  25

/* Append an auxv (tag, val) pair. */
static long * push_auxv(long * sp, long tag, long val) {
    *sp++ = tag;
    *sp++ = val;
    return sp;
}

/* Call a single init/fini function. Signature per gabi 08:
 *   void (*)(int argc, char **argv, char **envp)
 * Most freestanding constructors ignore the args; we pass minimal
 * `(0, NULL, NULL)`. Returns normally so `Load` can iterate. */
LEAN_EXPORT lean_object * leanload_exec_call_ctor(uint64_t addr,
                                                  lean_object * /* w */) {
    if (addr == 0) return leanload_io_err("call_ctor: null address");
    typedef void (*ctor_t)(int, char **, char **);
    ((ctor_t)(uintptr_t)addr)(0, NULL, NULL);
    return lean_io_result_mk_ok(lean_box(0));
}

LEAN_EXPORT lean_object * leanload_exec_run(
    uint64_t entry,
    uint64_t phdr_va,    /* AT_PHDR  */
    uint64_t phent,      /* AT_PHENT */
    uint64_t phnum,      /* AT_PHNUM */
    uint64_t base_va,    /* AT_BASE; 0 if not applicable */
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

    /* Layout from top of region: argv0 string, then 16 random bytes
     * for AT_RANDOM, then the SP-relative array. */
    char * top = (char *)sr->addr + sr->length;
    char * argv0_dst = top - argv0_len;
    memcpy(argv0_dst, argv0, argv0_len);

    /* AT_RANDOM points to 16 caller-provided bytes; fill them with a
     * non-zero pattern. (Real ld.so reads /dev/urandom; for now the
     * stack canary is just deterministic.) */
    char * random_dst = argv0_dst - 16;
    random_dst = (char *)((uintptr_t)random_dst & ~(uintptr_t)15);
    for (int i = 0; i < 16; i++) random_dst[i] = (char)(0xa5 ^ i);

    /* Reserve space for argc(1) + argv(2) + envp(1) + auxv pairs.
     * 7 auxv pairs + AT_NULL = 8 pairs = 16 longs. Total ~20 longs. */
    uintptr_t after_data = (uintptr_t)random_dst & ~(uintptr_t)15;
    long * sp = (long *)(after_data - 16 * 24);
    sp = (long *)((uintptr_t)sp & ~(uintptr_t)15);

    long * w = sp;
    *w++ = 1;                   /* argc                       */
    *w++ = (long)argv0_dst;     /* argv[0]                    */
    *w++ = 0;                   /* argv[1] = NULL             */
    *w++ = 0;                   /* envp[0] = NULL             */

    /* auxv */
    if (phdr_va) {
        w = push_auxv(w, AT_PHDR,   (long)phdr_va);
        w = push_auxv(w, AT_PHENT,  (long)phent);
        w = push_auxv(w, AT_PHNUM,  (long)phnum);
    }
    w = push_auxv(w, AT_PAGESZ,  4096);
    if (base_va) w = push_auxv(w, AT_BASE, (long)base_va);
    w = push_auxv(w, AT_ENTRY,   (long)entry);
    w = push_auxv(w, AT_RANDOM,  (long)random_dst);
    w = push_auxv(w, AT_NULL,    0);

#if defined(__aarch64__)
    asm volatile(
        "mov sp, %0\n"
        "br  %1\n"
        :
        : "r"(sp), "r"(entry)
        : "memory");
#else
# error "leanload_exec_run: only AArch64 implemented"
#endif
    __builtin_unreachable();
}
