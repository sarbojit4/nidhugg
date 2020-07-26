typedef unsigned long int qthread_t;

int qthread_create(qthread_t *tid, void *(*func)(void *), void *);
void qthread_wait(qthread_t tid, void *ret_val);
void qthread_start(qthread_t tid);
void qthread_post_event(qthread_t tid, void *(*func)(void *), void *); 
int qthread_exec();
