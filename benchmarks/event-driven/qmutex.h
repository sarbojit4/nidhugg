#include <pthread.h>
#include <stdbool.h>
#include "qthread.h"

typedef struct qmutex {
    qthread_t qt;
} qmutex;

struct __qmutex_closure_arg {
    pthread_mutex_t mutex;
    pthread_cond_t cond;
    bool done;
    void *(*func)(void *);
    void *arg, *res;
};

static inline void *__qmutex_handler(void *arg) {
    qthread_exec();
    return arg;
}

static inline void *__qmutex_message(void *voidp_arg) {
    struct __qmutex_closure_arg *arg = voidp_arg;
    pthread_mutex_lock(&arg->mutex);
    arg->res = arg->func(arg->arg);
    arg->done = true;
    pthread_cond_signal(&arg->cond);
    pthread_mutex_unlock(&arg->mutex);
    return NULL;
}

static inline int qmutex_init(qmutex *mutex) {
    qthread_create(&mutex->qt, __qmutex_handler, NULL);
    qthread_start(mutex->qt);
    return 0;
}

/* Equivalent to (hypothetical)
 *   lock()
 *   func(farg)
 *   unlock()
 *
 * Aside from silly details like the return value of pthread_self()
 */
static inline void *qmutex_delegate(qmutex *mutex, void *(*func)(void *), void *farg) {
    struct __qmutex_closure_arg arg;
    arg.func = func;
    arg.arg = farg;
    arg.done = false;
    pthread_mutex_init(&arg.mutex, NULL);
    pthread_cond_init(&arg.cond, NULL);
    pthread_mutex_lock(&arg.mutex);
    qthread_post_event(mutex->qt, __qmutex_message, &arg);
    /* Loop only needed due to posix semantics specifying that cond_wait can be
     * awoken spuriously. We assume this is not tested by Nidhugg-like SMC
     * tools.
     */
    while (!arg.done) {
        pthread_cond_wait(&arg.cond, &arg.mutex);
    }
    return arg.res;
}

/* We don't model this with enough fidelity to catch, f.ex. destroy-delegate
 * races. */
static inline int qmutex_destroy(qmutex *mutex) {
    /* What do you mean there's no way to stop a qthread? */
    return 0;
}
