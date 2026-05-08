/* Runtime IO shims: file ops + memory ops in one translation unit.
 *
 * `FileHandle` is the only Lean-visible opaque artifact (wraps a
 * kernel fd). All memory addresses cross the boundary as `uint64_t`;
 * the kernel address space is the lookup table, so there's no
 * Lean-side region handle.
 *
 * Bounds proofs live entirely on the Lean side
 * (`Layout.patch_inRange` etc.); externs trust addresses computed
 * by the safe `Layout.Region.*` wrappers in Lean.
 */

#include "runtime.h"
#include <errno.h>
#include <fcntl.h>
#include <stdlib.h>
#include <string.h>
#include <sys/mman.h>
#include <unistd.h>

/* ------------------------------------------------------------------ */
/* FileHandle external-object plumbing                                 */
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
/* File operations                                                     */
/* ------------------------------------------------------------------ */

/* Open a file read-only, return its `FileHandle`. Finalizer closes
 * the fd on Lean GC. */
LEAN_EXPORT lean_object * leanload_open(b_lean_obj_arg path_obj,
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
 * Loops on short reads. */
LEAN_EXPORT lean_object * leanload_pread(b_lean_obj_arg hobj,
                                         uint64_t offset,
                                         uint64_t len,
                                         lean_object * /* w */) {
    leanload_filehandle * h = (leanload_filehandle *)lean_get_external_data(hobj);
    if (h->fd < 0) return leanload_io_err("filehandle: closed");
    lean_object * arr = lean_alloc_sarray(/*elem_size=*/1, /*size=*/(size_t)len, /*cap=*/(size_t)len);
    uint8_t * buf = lean_sarray_cptr(arr);
    size_t got = 0;
    while (got < (size_t)len) {
        ssize_t n = pread(h->fd, buf + got, (size_t)len - got, (off_t)(offset + got));
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

/* ------------------------------------------------------------------ */
/* Memory operations                                                   */
/* ------------------------------------------------------------------ */

/* File-backed `MAP_PRIVATE | MAP_FIXED` overlay at `vaddr`. */
LEAN_EXPORT lean_object * leanload_mmap_file(b_lean_obj_arg hobj,
                                             uint64_t vaddr,
                                             uint64_t len,
                                             uint32_t prot,
                                             uint64_t offset,
                                             lean_object * /* w */) {
    leanload_filehandle * h = (leanload_filehandle *)lean_get_external_data(hobj);
    if (h->fd < 0) return leanload_io_err("filehandle: closed");
    void * p = mmap((void *)(uintptr_t)vaddr, (size_t)len, (int)prot,
                    MAP_PRIVATE | MAP_FIXED, h->fd, (off_t)offset);
    if (p == MAP_FAILED) {
        return leanload_io_err(strerror(errno));
    }
    return lean_io_result_mk_ok(lean_box(0));
}

/* Anonymous private mapping pinned at `vaddr` (`MAP_FIXED`). */
LEAN_EXPORT lean_object * leanload_mmap_reserve(uint64_t vaddr,
                                                uint64_t len,
                                                lean_object * /* w */) {
    void * p = mmap((void *)(uintptr_t)vaddr, (size_t)len,
                    PROT_READ | PROT_WRITE,
                    MAP_PRIVATE | MAP_ANONYMOUS | MAP_FIXED, -1, 0);
    if (p == MAP_FAILED) {
        return leanload_io_err(strerror(errno));
    }
    return lean_io_result_mk_ok(lean_box(0));
}

/* Anonymous `MAP_STACK` mapping; kernel chooses the address. Returns
 * the chosen base — caller threads it to `exec_run`. */
LEAN_EXPORT lean_object * leanload_mmap_stack(uint64_t len,
                                              lean_object * /* w */) {
    void * p = mmap(NULL, (size_t)len,
                    PROT_READ | PROT_WRITE,
                    MAP_PRIVATE | MAP_ANONYMOUS | MAP_STACK, -1, 0);
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

/* Write 8 little-endian bytes of `value` at `addr`. */
LEAN_EXPORT lean_object * leanload_patch64(uint64_t addr,
                                           uint64_t value,
                                           lean_object * /* w */) {
    memcpy((void *)(uintptr_t)addr, &value, 8);
    return lean_io_result_mk_ok(lean_box(0));
}

/* Write the low 4 little-endian bytes of `value` at `addr`. */
LEAN_EXPORT lean_object * leanload_patch32(uint64_t addr,
                                           uint64_t value,
                                           lean_object * /* w */) {
    uint32_t lo = (uint32_t)value;
    memcpy((void *)(uintptr_t)addr, &lo, 4);
    return lean_io_result_mk_ok(lean_box(0));
}

/* Zero `len` bytes starting at `addr`. */
LEAN_EXPORT lean_object * leanload_zeroout(uint64_t addr,
                                           uint64_t len,
                                           lean_object * /* w */) {
    memset((void *)(uintptr_t)addr, 0, (size_t)len);
    return lean_io_result_mk_ok(lean_box(0));
}
