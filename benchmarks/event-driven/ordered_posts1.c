#include <stdio.h>
#include <stdatomic.h>
#include <pthread.h>
#include "qthread.h"

//N! trace

#ifndef N
#  warning "N was not defined; defining it as 2"
#  define N 5
#endif

qthread_t handler;

atomic_int x;
void *mes(void *j){
  atomic_store_explicit(&x, 2, memory_order_seq_cst);
  return 0;
}

void *th_post(void *i){
  for (int j = 0; j < N; j++){
    qthread_post_event(handler, &mes, &j);
  }
  return 0;
}

void *handler_func(void *i){ 
  int quit = qthread_exec();
  return 0;
}

int main(){
  pthread_t t;
  qthread_create(&handler, &handler_func, NULL);
  qthread_start(handler);
  pthread_create(&t, NULL, &th_post, NULL);
  pthread_join(t, NULL);
  qthread_wait(handler, NULL);
}
