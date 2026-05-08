/* LeanLoad runtime shims: trust seam between Lean and the kernel.
 *
 * Two topic groups:
 *   1. Memory operations (region.c) — mmap variants, mprotect, raw
 *      writes. All addresses are `uint64_t`; the kernel address space
 *      is the lookup table. Mappings live for the process lifetime
 *      (no munmap; kernel reclaims at exit).
 *   2. Control transfer (exec.c) — leanload_exec_run builds the stack
 *      a kernel-`exec`'d process would see (argc/argv/envp/auxv) at a
 *      caller-supplied address, switches SP, and jumps to entry. Does
 *      not return.
 *
 * FileHandle (file.c) is the only opaque Lean external object —
 * wraps an open fd so Lean can pread / mmap from it without
 * re-opening per call.
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

/* Wrap a C string as a `lean_io_result_mk_error`. */
static inline lean_object * leanload_io_err(const char * msg) {
    return lean_io_result_mk_error(
        lean_mk_io_user_error(lean_mk_string(msg)));
}

/* ------------------------------------------------------------------ */
/* FileHandle (file.c)                                                 */
/* ------------------------------------------------------------------ */

typedef struct {
    int fd;          /* open(2)'d read-only fd, or -1 if closed */
} leanload_filehandle;

/* Lean external_class for FileHandle. The finalizer closes the fd. */
lean_external_class * leanload_filehandle_class(void);

#ifdef __cplusplus
}
#endif

#endif
