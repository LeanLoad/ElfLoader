#include <stdio.h>

void libunused_print(void) {
    printf("[libunused] function\n");
}

__attribute__((constructor))
static void libunused_ctor(void) {
    printf("[libunused] ctor\n");
}
