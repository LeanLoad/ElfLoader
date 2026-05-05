#include <stdio.h>
#include <pthread.h>
#include <string.h>
#include <stdlib.h>
#include "libfoo.h"
#include "libbar.h"

#define panic(...)            \
    do {                      \
        printf(__VA_ARGS__);  \
        exit(1);              \
    } while (0)

static __thread int tls;

__attribute__((constructor))
static void main_ctor(void) {
    printf("[main] ctor\n");
}

static void *thread_entry(void *arg) {
    (void)arg;
    printf("[thread] tls=%d, &tls=%p\n", tls, &tls);
    tls = 99;
    printf("[thread] tls=%d, &tls=%p\n", tls, &tls);
    fflush(stdout);
    return NULL;
}

static void test_pthread(void) {
    pthread_t tid;
    tls = 42;
    printf("[main] tls=%d, &tls=%p\n", tls, &tls);

    int rc = pthread_create(&tid, NULL, thread_entry, NULL);
    if (rc != 0) {
        panic("[main] pthread_create failed rc=%d (%s)\n", rc, strerror(rc));
    }

    rc = pthread_join(tid, NULL);
    if (rc != 0) {
        panic("[main] pthread_join failed rc=%d (%s)\n", rc, strerror(rc));
    }

    printf("[main] tls=%d, &tls=%p\n", tls, &tls);
}

int main(void) {
    printf("[main] entry\n");
    libfoo_print();
    libbar_step(3);

    printf("[main] pthread test start\n");
    test_pthread();
    printf("[main] pthread test completed\n");

    printf("[main] exit\n");
    return 0;
}
