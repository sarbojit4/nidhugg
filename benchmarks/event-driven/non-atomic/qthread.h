typedef pthread_mutex_t *qthread_t;

typedef struct msg_arg_t{
  void *(*func)(void *);
  void *arg;
  qthread_t tid;
} msg_arg_t;

int qthread_create(qthread_t *tid, void *(*func)(void *), void * arg){
  pthread_mutex_t mtx;
  int ret = pthread_mutex_init(&mtx,NULL);
  *tid = &mtx;
  return ret;
}
void qthread_wait(qthread_t tid, void *ret_val){}
void qthread_start(qthread_t tid){}
void *msg_func(void *_msg_arg){
  void *(*func)(void *) = (*(msg_arg_t *)_msg_arg).func;
  void *arg = (*(msg_arg_t *)_msg_arg).arg;
  qthread_t tid = (*(msg_arg_t *)_msg_arg).tid;
  pthread_mutex_lock(tid);
  (*func)(arg);
  pthread_mutex_unlock(tid);
  return NULL;
}
void qthread_post_event(qthread_t tid, void *(*func)(void *), void *arg){
  pthread_t msg;
  msg_arg_t msg_arg = {func,arg,tid};
  pthread_create(&msg,NULL,&msg_func,&msg_arg);
}
int qthread_exec(){return 0;}
