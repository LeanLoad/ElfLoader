/* Memory region: a foreign-owned mmap'd buffer.
 *
 * Wrapped in a Lean external object (`LeanLoad.Region.Region`).
 * Mappings live for the lifetime of the process — the finalizer
 * deliberately does NOT `munmap` (see `leanload_region_finalize`
 * in region.c); the kernel reclaims at exit. Users read/write via
 * the helpers in `LeanLoad.Region`.
 */

#ifndef LEANLOAD_REGION_H
#define LEANLOAD_REGION_H

#include "common.h"
#include <stddef.h>

#ifdef __cplusplus
extern "C" {
#endif

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
