/* LeanLoad runtime shims: trust seam between Lean and the kernel.
 *
 * Two topic groups:
 *   1. Memory regions (region.c) — opaque mmap'd handles wrapped as
 *      Lean external objects (LeanLoad.Runtime.Region). Mappings live
 *      for the lifetime of the process; the finalizer deliberately
 *      does NOT munmap (the kernel reclaims at exit).
 *   2. Control transfer (exec.c) — leanload_exec_run builds the stack
 *      a kernel-`exec`'d process would see (argc/argv/envp/auxv) on a
 *      caller-supplied region, switches SP, and jumps to entry. Does
 *      not return.
 *
 * Audited by inspection (~150 lines of C), not proven.
 */

#ifndef LEANLOAD_RUNTIME_H
#define LEANLOAD_RUNTIME_H

#include <lean/lean.h>
#include <stddef.h>
#include <stdint.h>

#ifdef __cplusplus
extern "C" {
#endif

/* ------------------------------------------------------------------ */
/* Helpers                                                             */
/* ------------------------------------------------------------------ */

/* Wrap a C string as a `lean_io_result_mk_error`. */
static inline lean_object * leanload_io_err(const char * msg) {
    return lean_io_result_mk_error(
        lean_mk_io_user_error(lean_mk_string(msg)));
}

/* ------------------------------------------------------------------ */
/* Region (region.c)                                                   */
/* ------------------------------------------------------------------ */

typedef struct {
    void * addr;     /* base address of the mapping (or NULL if unmapped) */
    size_t length;   /* mapping length in bytes                            */
} leanload_region;

/* Lean external_class for region handles. Allocated on first use. */
lean_external_class * leanload_region_class(void);

#ifdef __cplusplus
}
#endif

#endif
