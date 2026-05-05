/* Region externs: mmap, munmap, mprotect, byte-level pokes.
 *
 * All addresses cross the Lean/C boundary as `uint64_t` (we deliberately
 * do not expose `void *` — Lean side reasons in terms of virtual
 * addresses produced by the planner).
 */

#include "region.h"
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
/* mmap: allocate a fresh region with the given permissions.
 *
 * Lean signature:
 *   leanload_region_mmap (vaddr : UInt64) (len : USize)
 *                        (prot flags : UInt32) : IO Region
 *
 * `vaddr=0` means "kernel chooses". `flags` is the raw mmap flags
 * value (e.g. MAP_PRIVATE | MAP_ANONYMOUS); the planner picks.
 */
LEAN_EXPORT lean_object * leanload_region_mmap(uint64_t vaddr,
                                               size_t   len,
                                               uint32_t prot,
                                               uint32_t flags,
                                               lean_object * /* world */) {
    void * hint = (vaddr == 0) ? NULL : (void *)(uintptr_t)vaddr;
    void * p = mmap(hint, len, (int)prot, (int)flags, -1, 0);
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

/* mprotect on the whole region. If transitioning to PROT_EXEC, also
 * flush instruction cache for the range — required on architectures
 * (notably aarch64) where I-cache and D-cache are not coherent and
 * code freshly written via D-cache is otherwise invisible to the
 * instruction fetcher.
 */
LEAN_EXPORT lean_object * leanload_region_mprotect(b_lean_obj_arg robj,
                                                   uint32_t prot,
                                                   lean_object * /* w */) {
    leanload_region * r = (leanload_region *)lean_get_external_data(robj);
    if (!r->addr) return leanload_io_err("region: not mapped");
    if (mprotect(r->addr, r->length, (int)prot) != 0) {
        return leanload_io_err(strerror(errno));
    }
    if (prot & PROT_EXEC) {
        char * start = (char *)r->addr;
        char * end   = start + r->length;
        __builtin___clear_cache(start, end);
    }
    return lean_io_result_mk_ok(lean_box(0));
}

/* mprotect on a sub-range of the region. Used when one big region
 * holds multiple PT_LOAD segments with different permissions. */
LEAN_EXPORT lean_object * leanload_region_mprotect_range(b_lean_obj_arg robj,
                                                         size_t offset,
                                                         size_t length,
                                                         uint32_t prot,
                                                         lean_object * /* w */) {
    leanload_region * r = (leanload_region *)lean_get_external_data(robj);
    if (!r->addr) return leanload_io_err("region: not mapped");
    if (offset > r->length || length > r->length - offset) {
        return leanload_io_err("mprotect_range: out of bounds");
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

/* Copy bytes from a Lean ByteArray into the region at `offset`. */
LEAN_EXPORT lean_object * leanload_region_write(b_lean_obj_arg robj,
                                                size_t offset,
                                                b_lean_obj_arg src,
                                                lean_object * /* w */) {
    leanload_region * r = (leanload_region *)lean_get_external_data(robj);
    if (!r->addr) return leanload_io_err("region: not mapped");
    size_t n = lean_sarray_size(src);
    if (offset > r->length || n > r->length - offset) {
        return leanload_io_err("region: write out of bounds");
    }
    memcpy((uint8_t *)r->addr + offset, lean_sarray_cptr(src), n);
    return lean_io_result_mk_ok(lean_box(0));
}

/* Return the base address of the region (as uint64_t). */
LEAN_EXPORT uint64_t leanload_region_base(b_lean_obj_arg robj) {
    leanload_region * r = (leanload_region *)lean_get_external_data(robj);
    return (uint64_t)(uintptr_t)r->addr;
}


