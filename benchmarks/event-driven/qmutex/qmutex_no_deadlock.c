#include <pthread.h>
#include <assert.h>
#include "qmutex.h"

static int count = 0;
static qmutex mutex;

static void *cs(void *arg) {
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
    qmutex_destroy(&mutex);
    assert(false && "We should reach here");
    return 0;
}
