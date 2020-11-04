#include <pthread.h>
#include <assert.h>
#include "qmutex.h"

static volatile int in_cs = 0;
int count = 0;
static qmutex mutex;

static void *cs(void *arg) {
    in_cs = 1;
    assert(in_cs);
    in_cs = 0;
    count++;
    return NULL;
}

static void *p(void *arg) {
    qmutex_delegate(&mutex, cs, NULL);
    return NULL;
}

int main() {
    pthread_t pt;
    qmutex_init(&mutex);
    pthread_create(&pt, NULL, p, NULL);
    qmutex_delegate(&mutex, cs, NULL);
    pthread_join(pt, NULL);
    assert(count == 2);
    qmutex_destroy(&mutex);
    return 0;
}
