/* FileHandle externs: opaque `int fd` wrapper.
 *
 * Lifetime: opened by `leanload_filehandle_open`, lives via Lean GC,
 * the finalizer closes the fd. Used by `Parse.File.parse` (per-section
 * pread) and by `Exec.realize` (file-backed mmap from the already-open
 * fd so we don't open/close once per segment).
 */

#include "runtime.h"
#include <errno.h>
#include <fcntl.h>
#include <stdlib.h>
#include <string.h>
#include <sys/mman.h>
#include <unistd.h>

/* ------------------------------------------------------------------ */
/* External-object plumbing                                            */
/* ------------------------------------------------------------------ */

static void leanload_filehandle_finalize(void * p) {
    leanload_filehandle * h = (leanload_filehandle *)p;
    if (h->fd >= 0) {
        close(h->fd);
        h->fd = -1;
    }
    free(h);
}

static void leanload_filehandle_foreach(void * p, b_lean_obj_arg f) {
    (void)p; (void)f;  /* no nested lean_object* */
}

static lean_external_class * g_filehandle_class = NULL;

lean_external_class * leanload_filehandle_class(void) {
    if (!g_filehandle_class) {
        g_filehandle_class = lean_register_external_class(
            leanload_filehandle_finalize,
            leanload_filehandle_foreach);
    }
    return g_filehandle_class;
}

/* ------------------------------------------------------------------ */
/* Operations                                                          */
/* ------------------------------------------------------------------ */

/* Open a file read-only, return its `FileHandle`. The fd is closed
 * by the finalizer when Lean GCs the handle. */
LEAN_EXPORT lean_object * leanload_filehandle_open(b_lean_obj_arg path_obj,
                                                        lean_object * /* w */) {
    const char * path = lean_string_cstr(path_obj);
    int fd = open(path, O_RDONLY | O_CLOEXEC);
    if (fd < 0) {
        return leanload_io_err(strerror(errno));
    }
    leanload_filehandle * h = (leanload_filehandle *)malloc(sizeof(*h));
    if (!h) {
        close(fd);
        return leanload_io_err("malloc failed");
    }
    h->fd = fd;
    return lean_io_result_mk_ok(
        lean_alloc_external(leanload_filehandle_class(), h));
}

/* `pread(2)` exactly `len` bytes at `offset` into a fresh ByteArray.
 * Short reads (kernel pages out, EOF mid-buffer) loop until satisfied
 * or an error / true EOF is hit. */
LEAN_EXPORT lean_object * leanload_filehandle_pread(b_lean_obj_arg hobj,
                                                    uint64_t offset,
                                                    size_t   len,
                                                    lean_object * /* w */) {
    leanload_filehandle * h = (leanload_filehandle *)lean_get_external_data(hobj);
    if (h->fd < 0) return leanload_io_err("filehandle: closed");
    lean_object * arr = lean_alloc_sarray(/*elem_size=*/1, /*size=*/len, /*cap=*/len);
    uint8_t * buf = lean_sarray_cptr(arr);
    size_t got = 0;
    while (got < len) {
        ssize_t n = pread(h->fd, buf + got, len - got, (off_t)(offset + got));
        if (n < 0) {
            if (errno == EINTR) continue;
            lean_dec_ref(arr);
            return leanload_io_err(strerror(errno));
        }
        if (n == 0) {
            lean_dec_ref(arr);
            return leanload_io_err("filehandle: short read (EOF)");
        }
        got += (size_t)n;
    }
    return lean_io_result_mk_ok(arr);
}

/* File-backed `MAP_PRIVATE | MAP_FIXED` at `vaddr` from this handle.
 * Returns a `Region` for the freshly mapped range (one mmap = one
 * Region — uniform with `mmap_reserve` and `mmap_stack` so the
 * abstract memory model can treat all kernel mappings the same).
 * `prot` is the final permissions; the caller owns the address
 * range (typically a sub-range of an anon reservation that this
 * overlays). */
LEAN_EXPORT lean_object * leanload_filehandle_mmap(b_lean_obj_arg hobj,
                                                      uint64_t vaddr,
                                                      size_t   len,
                                                      uint32_t prot,
                                                      uint64_t offset,
                                                      lean_object * /* w */) {
    leanload_filehandle * h = (leanload_filehandle *)lean_get_external_data(hobj);
    if (h->fd < 0) return leanload_io_err("filehandle: closed");
    void * p = mmap((void *)(uintptr_t)vaddr, len, (int)prot,
                    MAP_PRIVATE | MAP_FIXED, h->fd, (off_t)offset);
    if (p == MAP_FAILED) {
        return leanload_io_err(strerror(errno));
    }
    leanload_region * r = (leanload_region *)malloc(sizeof(*r));
    if (!r) {
        munmap(p, len);
        return leanload_io_err("malloc failed");
    }
    r->addr   = p;
    r->length = len;
    return lean_io_result_mk_ok(
        lean_alloc_external(leanload_region_class(), r));
}
