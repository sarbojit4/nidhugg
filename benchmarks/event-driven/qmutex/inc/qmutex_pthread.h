#include <pthread.h>
#include <stdbool.h>

typedef pthread_mutex_t qmutex;

static inline int qmutex_init(qmutex *mutex) {
  return pthread_mutex_init(mutex, NULL);
}

/* Equivalent to (hypothetical)
 *   lock()
 *   func(farg)
 *   unlock()
 */
static inline void *qmutex_delegate(qmutex *mutex, void *(*func)(void *), void *farg) {
  pthread_mutex_lock(mutex);
  void *ret = func(farg);
  pthread_mutex_unlock(mutex);
  return ret;
}

/* We don't model this with enough fidelity to catch, f.ex. destroy-delegate
 * races. */
static inline int qmutex_destroy(qmutex *mutex) {
  pthread_mutex_destroy(mutex);
  return 0;
}
