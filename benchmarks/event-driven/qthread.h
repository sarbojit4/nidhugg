#ifndef __QTHREAD_H__
#define __QTHREAD_H__

#include <stdlib.h>
#include <pthread.h>
#include <stdio.h>

/* This header implements a compatibility layer, allowing a qthread
 * program to run either on qthreads or on pthreads.
 * When running on pthreads, qthread handlers are modelled as mutexes,
 * and posting an event instead creates a thread that acquires the mutex
 * before executing the message payload.
 *
 * The model is designed with benchmarking fairness as a primary goal.
 * Even when running on qthreads, the benchmark will make almost the
 * same sequence of events, except omitting mutex lock/unlock, and
 * performing qthread_post_event instead of pthread_create.
 *
 * When running on qthreads, the real qthreads functions (not the ones
 * we redirect to with ifdefs) will be intercepted by nidhugg (or other
 * event-aware tool), instead of calling the stubs we have in this file.
 *
 * The header is also designed to be a drop-in replacement for the
 * "standard" qthread header, using #defines to redirect calls to
 * qthread functions to its own.
 */

/* The native qthread handler type */
typedef unsigned long int _actual_qthread_t;

/* The handler type that is exposed by our compatibility layer */
typedef struct {
  pthread_mutex_t mutex;
  _actual_qthread_t qthread;
  int is_pthread;
} *qthread_t;

/* The payload type passed to our messages */
struct _msg_arg {
  void (*func)(void *);
  void *arg;
  qthread_t tid;
};

#define _MAGIC_I_AM_NOT_INTERCEPTED -42

int qthread_create(_actual_qthread_t *tid, void *(*func)(void *), void * arg){
  *tid = 0xdeadbeefdeadbeef;
  return _MAGIC_I_AM_NOT_INTERCEPTED;
}
static int qthread_create_internal(qthread_t *tid, void *(*func)(void *), void * arg){
  *tid = malloc(sizeof(**tid));
  int ret = pthread_mutex_init(&(*tid)->mutex,NULL);
  if (ret) return ret;
  ret = qthread_create(&(*tid)->qthread, func, arg);
  (*tid)->is_pthread = (ret == _MAGIC_I_AM_NOT_INTERCEPTED);
  if ((*tid)->is_pthread) return 0;
  else return ret;
}

static void qthread_wait_internal(qthread_t tid, void *ret_val){
  /* Empty; we choose not to model wait
   *
   * Note that this means that wait will not wait but return
   * immediately.
   */
}

void qthread_start(_actual_qthread_t tid){}
static void qthread_start_internal(qthread_t tid){
  qthread_start(tid->qthread);
}

static void *_pthread_func(void *_msg_arg){
  struct _msg_arg *msg_arg = (struct _msg_arg *)_msg_arg;
  void (*func)(void *) = msg_arg->func;
  void *arg = msg_arg->arg;
  pthread_mutex_t *mutex = &msg_arg->tid->mutex;
  pthread_mutex_lock(mutex);
  (*func)(arg);
  pthread_mutex_unlock(mutex);
  free(msg_arg);
  return NULL;
}
static void _post_func(void *_msg_arg){
  /* Replicate the actions of _pthread_func as much as possible */
  struct _msg_arg *msg_arg = (struct _msg_arg *)_msg_arg;
  void (*func)(void *) = msg_arg->func;
  void *arg = msg_arg->arg;
  pthread_mutex_t *mutex = &msg_arg->tid->mutex;
  (void)mutex; // no lock
  (*func)(arg);
  (void)mutex; // no unlock
  free(msg_arg);
}
void qthread_post_event(_actual_qthread_t tid, void (*func)(void *), void *arg){}
static void qthread_post_event_internal(qthread_t tid, void (*func)(void *), void *arg){
  pthread_t msg;
  struct _msg_arg *msg_arg = malloc(sizeof(struct _msg_arg));
  msg_arg->func = func;
  msg_arg->arg = arg;
  msg_arg->tid = tid;
  if (tid->is_pthread)
    pthread_create(&msg,NULL,_pthread_func,msg_arg);
  else
    qthread_post_event(tid->qthread,_post_func,msg_arg);
}

int qthread_exec(){
  return 0;
}

/* Redirect calls to these qthreads functions */
#define qthread_create qthread_create_internal
#define qthread_start qthread_start_internal
#define qthread_post_event qthread_post_event_internal
#define qthread_wait qthread_wait_internal

#endif /* !defined(__QTHREAD_H__) */
