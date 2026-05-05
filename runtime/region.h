/* Memory region: a foreign-owned mmap'd buffer.
 *
 * Wrapped in a Lean external object (`LeanLoad.FFI.Region.Region`).
 * The finalizer calls munmap; users read/write via the helpers in
 * `LeanLoad.FFI.Region`.
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
