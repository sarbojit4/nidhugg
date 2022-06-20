#include<stdlib.h>
typedef pthread_mutex_t *qthread_t;

typedef struct{
  void (*func)(void *);
  void *arg;
  qthread_t tid;
} msg_arg_t;

int qthread_create(qthread_t *tid, void *(*func)(void *), void * arg){
  pthread_mutex_t *mtx=malloc(sizeof(pthread_mutex_t));
  int ret = pthread_mutex_init(mtx,NULL);
  *tid = mtx;
  return ret;
}
void qthread_wait(qthread_t tid, void *ret_val){
  //free(tid);
}
void qthread_start(qthread_t tid){}
void *msg_func(void *_msg_arg){
  msg_arg_t *msg_arg = (msg_arg_t *)_msg_arg;
  void (*func)(void *) = msg_arg->func;
  void *arg = msg_arg->arg;
  qthread_t tid = msg_arg->tid;
  pthread_mutex_lock(tid);
  (*func)(arg);
  pthread_mutex_unlock(tid);
  free(msg_arg);
  return NULL;
}
void qthread_post_event(qthread_t tid, void (*func)(void *), void *arg){
  pthread_t msg;
  msg_arg_t *msg_arg = malloc(sizeof(msg_arg_t));
  msg_arg->func = func;
  msg_arg->arg = arg;
  msg_arg->tid = tid;
  pthread_create(&msg,NULL,&msg_func,msg_arg);
}
int qthread_exec(){return 0;}

