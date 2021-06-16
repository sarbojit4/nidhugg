typedef unsigned long int qthread_t;

int qthread_create(qthread_t *tid, void *(*func)(void *), void *);
void qthread_wait(qthread_t tid, void *ret_val){
  pthread_join(tid, ret_val);
}
void qthread_start(qthread_t tid);
void qthread_post_event(qthread_t tid, void *(*func)(void *), void *); 
void qthread_quit(qthread_t handler);
int qthread_exec();
