#include<stdio.h>
#include<stdatomic.h>
#include<pthread.h>
//using namespace std;
int qthread_create(int *tid, void *(*func)(void *), void *);
void qthread_wait(int tid, void *ret_val);
void qthread_start(int tid);
void qthread_post_event(int tid, void *(*func)(void *), void *); 
int qthread_exec();

#ifndef N
#  warning "N was not defined"
#  define N 2
#endif

atomic_int g;
void *mes(void *j){
 atomic_store_explicit(&g, *(atomic_int *)j, memory_order_seq_cst);
 return 0;
}

void *th_post(void *i){
  qthread_post_event(1, &mes, &i); 
  return 0;
}

void *handler_func(void *i){ 
  int quit = qthread_exec();
  return 0;
}

int main() {
  pthread_t t[N];
  int handler;

  qthread_create(&handler, &handler_func, NULL);
  for (int i = 0; i < N; i++){
    pthread_create(&t[i], NULL, &th_post, &i);
  }
  for (int i = 0; i < N; i++){
    pthread_join(t[i], NULL);
  }
  qthread_start(handler);
  qthread_wait(handler, NULL);
}
