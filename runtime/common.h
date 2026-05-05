/* Helpers shared across the LeanLoad runtime shims. */

#ifndef LEANLOAD_COMMON_H
#define LEANLOAD_COMMON_H

#include <lean/lean.h>

#ifdef __cplusplus
extern "C" {
#endif

/* Wrap a C string as a `lean_io_result_mk_error`. */
static inline lean_object * leanload_io_err(const char * msg) {
    return lean_io_result_mk_error(
        lean_mk_io_user_error(lean_mk_string(msg)));
}

#ifdef __cplusplus
}
#endif

#endif
