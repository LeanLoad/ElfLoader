/* Region externs: mmap variants + per-range operations.
 *
 * All addresses cross the Lean/C boundary as `uint64_t` (we deliberately
 * do not expose `void *` — Lean side reasons in terms of virtual
 * addresses produced by the planner).
 *
 * File-backed mmap from an already-open `FileHandle` lives in
 * `file.c` so the two concepts (memory ranges vs. open files) are
 * each in their own translation unit.
 */

#include "runtime.h"
#include <errno.h>
#include <stdlib.h>
#include <string.h>
#include <sys/mman.h>

/* ------------------------------------------------------------------ */
/* External-object plumbing                                            */
/* ------------------------------------------------------------------ */

static void leanload_region_finalize(void * p) {
    /* Do **not** `munmap`. Mappings are part of the loaded image (or
     * its supporting infrastructure: stack, etc.) and should live
     * for the lifetime of the process, exactly as `execve(2)` would
     * leave them. The kernel reclaims at process exit. We just free
     * the small bookkeeping struct.
     *
     * If a future caller needs explicit teardown (e.g. an `--inspect`
     * mode that loads, examines, and discards), it should call an
     * explicit `unmap` operation rather than relying on GC. */
    free(p);
}

static void leanload_region_foreach(void * p, b_lean_obj_arg f) {
    /* Region holds no nested lean_object*. No-op. */
    (void)p; (void)f;
}

static lean_external_class * g_class = NULL;

lean_external_class * leanload_region_class(void) {
    if (!g_class) {
        g_class = lean_register_external_class(
            leanload_region_finalize,
            leanload_region_foreach);
    }
    return g_class;
}

/* ------------------------------------------------------------------ */
/* mmap variants (anonymous; file-backed lives in file.c).             */
/* ------------------------------------------------------------------ */

static lean_object * mmap_rw(uint64_t vaddr, size_t len, int flags) {
    void * hint = (vaddr == 0) ? NULL : (void *)(uintptr_t)vaddr;
    void * p = mmap(hint, len, PROT_READ | PROT_WRITE, flags, -1, 0);
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

/* Anonymous private mapping pinned at `vaddr` (`MAP_FIXED`). Used by
 * Map as the per-object reservation at the Layout-assigned base. */
LEAN_EXPORT lean_object * leanload_region_mmap_reserve(uint64_t vaddr,
                                                          size_t   len,
                                                          lean_object * /* w */) {
    return mmap_rw(vaddr, len, MAP_PRIVATE | MAP_ANONYMOUS | MAP_FIXED);
}

/* Anonymous private stack mapping (`MAP_STACK`). Hints to the kernel
 * that the mapping will be used as a thread/process stack; a no-op on
 * Linux but documented as the right thing per `mmap(2)`. */
LEAN_EXPORT lean_object * leanload_region_mmap_stack(size_t len,
                                                     lean_object * /* w */) {
    return mmap_rw(0, len, MAP_PRIVATE | MAP_ANONYMOUS | MAP_STACK);
}

/* ------------------------------------------------------------------ */
/* mprotect + write at raw addresses                                   */
/* ------------------------------------------------------------------ */

/* mprotect on a sub-range of a region. Used when one big region holds
 * multiple `PT_LOAD` segments with different permissions. */
LEAN_EXPORT lean_object * leanload_region_mprotect(b_lean_obj_arg robj,
                                                         size_t offset,
                                                         size_t length,
                                                         uint32_t prot,
                                                         lean_object * /* w */) {
    leanload_region * r = (leanload_region *)lean_get_external_data(robj);
    if (offset > r->length || length > r->length - offset) {
        return leanload_io_err("mprotect: out of bounds");
    }
    char * start = (char *)r->addr + offset;
    if (mprotect(start, length, (int)prot) != 0) {
        return leanload_io_err(strerror(errno));
    }
    if (prot & PROT_EXEC) {
        __builtin___clear_cache(start, start + length);
    }
    return lean_io_result_mk_ok(lean_box(0));
}

/* Write 8 little-endian bytes of `value` to `region` at `offset`. */
LEAN_EXPORT lean_object * leanload_region_patch64(b_lean_obj_arg robj,
                                                  size_t offset,
                                                  uint64_t value,
                                                  lean_object * /* w */) {
    leanload_region * r = (leanload_region *)lean_get_external_data(robj);
    if (offset > r->length || 8 > r->length - offset) {
        return leanload_io_err("region: patch64 out of bounds");
    }
    /* unaligned little-endian write; assumes host is little-endian
     * (which both x86-64 and AArch64 in our supported configs are). */
    memcpy((uint8_t *)r->addr + offset, &value, 8);
    return lean_io_result_mk_ok(lean_box(0));
}

/* Write the low 4 little-endian bytes of `value` to `region` at `offset`. */
LEAN_EXPORT lean_object * leanload_region_patch32(b_lean_obj_arg robj,
                                                  size_t offset,
                                                  uint64_t value,
                                                  lean_object * /* w */) {
    leanload_region * r = (leanload_region *)lean_get_external_data(robj);
    if (offset > r->length || 4 > r->length - offset) {
        return leanload_io_err("region: patch32 out of bounds");
    }
    uint32_t lo = (uint32_t)value;
    memcpy((uint8_t *)r->addr + offset, &lo, 4);
    return lean_io_result_mk_ok(lean_box(0));
}

/* Zero `len` bytes in `region` starting at `offset`. */
LEAN_EXPORT lean_object * leanload_region_zeroout(b_lean_obj_arg robj,
                                                  size_t offset,
                                                  size_t len,
                                                  lean_object * /* w */) {
    leanload_region * r = (leanload_region *)lean_get_external_data(robj);
    if (offset > r->length || len > r->length - offset) {
        return leanload_io_err("region: zeroout out of bounds");
    }
    memset((uint8_t *)r->addr + offset, 0, len);
    return lean_io_result_mk_ok(lean_box(0));
}
