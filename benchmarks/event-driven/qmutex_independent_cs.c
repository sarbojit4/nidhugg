#include <pthread.h>
#include <assert.h>
#include "qmutex.h"

int x = 0, y = 0;
static qmutex mutex;

static void *cs(void *arg) {
    int *p = arg;
    (*p)++;
    return NULL;
}

static void *p(void *arg) {
    qmutex_delegate(&mutex, cs, (int*)&y);
    return NULL;
}

int main() {
    pthread_t pt;
    qmutex_init(&mutex);
    pthread_create(&pt, NULL, p, NULL);
    qmutex_delegate(&mutex, cs, (int*)&x);
    pthread_join(pt, NULL);
    assert(x == 1 && y == 1);
    qmutex_destroy(&mutex);
    return 0;
}
