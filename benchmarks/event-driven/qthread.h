#ifndef __QTHREAD_H__
#define __QTHREAD_H__

#include <stdlib.h>
#include <pthread.h>

typedef struct {
  pthread_mutex_t mutex;
  pthread_t qthread;
  int is_pthread;
} *qthread_t;

typedef struct{
  void (*func)(void *);
  void *arg;
  qthread_t tid;
} msg_arg_t;

int qthread_create(pthread_t *tid, void *(*func)(void *), void * arg){
  return 1;
}
int qthread_create_internal(qthread_t *tid, void *(*func)(void *), void * arg){
  *tid = malloc(sizeof(**tid));
  int ret = pthread_mutex_init(&(*tid)->mutex,NULL);
  (*tid)->is_pthread = qthread_create(&(*tid)->qthread, func, arg);
  return ret;
}
void qthread_wait_internal(qthread_t tid, void *ret_val){
  /* Empty; we choose not to model wait */
}
void qthread_start(pthread_t tid){}
void qthread_start_internal(qthread_t tid){
  qthread_start(tid->qthread);
}
void *msg_func(void *_msg_arg){
  msg_arg_t *msg_arg = (msg_arg_t *)_msg_arg;
  void (*func)(void *) = msg_arg->func;
  void *arg = msg_arg->arg;
  pthread_mutex_t *mutex = &msg_arg->tid->mutex;
  pthread_mutex_lock(mutex);
  (*func)(arg);
  pthread_mutex_unlock(mutex);
  free(msg_arg);
  return NULL;
}
void *post_func(void *_msg_arg){
  msg_arg_t *msg_arg = (msg_arg_t *)_msg_arg;
  void (*func)(void *) = msg_arg->func;
  void *arg = msg_arg->arg;
  pthread_mutex_t *mutex = &msg_arg->tid->mutex;
  (void)mutex; // no lock
  (*func)(arg);
  (void)mutex; // no unlock
  free(msg_arg);
  return NULL;
}
void qthread_post_event(pthread_t tid, void (*func)(void *), void *arg){
}
void qthread_post_event_internal(qthread_t tid, void (*func)(void *), void *arg){
  pthread_t msg;
  msg_arg_t *msg_arg = malloc(sizeof(msg_arg_t));
  msg_arg->func = func;
  msg_arg->arg = arg;
  msg_arg->tid = tid;
  if (tid->is_pthread)
    pthread_create(&msg,NULL,&msg_func,msg_arg);
  else
    qthread_post_event(tid->qthread,post_func,msg_arg);
}
int qthread_exec(){return 0;}

#define qthread_create qthread_create_internal
#define qthread_start qthread_start_internal
#define qthread_post_event qthread_post_event_internal
#define qthread_wait qthread_wait_internal

#endif /* !defined(__QTHREAD_H__) */
