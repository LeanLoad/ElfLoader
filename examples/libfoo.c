#include <stdio.h>
#include "libfoo.h"

void libfoo_print(void) {
    printf("[libfoo] function\n");
}

__attribute__((constructor))
static void libfoo_ctor(void) {
    printf("[libfoo] ctor\n");
}
