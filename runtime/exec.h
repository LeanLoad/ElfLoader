/* Hand control of the process to a loaded ELF image.
 *
 * `leanload_exec_run` builds the stack a kernel-`exec`'d process would
 * see (argc, argv[], envp[], auxv[]) on a caller-supplied region,
 * switches SP, and jumps to entry. Does not return.
 */

#ifndef LEANLOAD_EXEC_H
#define LEANLOAD_EXEC_H

#include "common.h"
#include <stdint.h>

#endif
