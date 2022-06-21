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
void mes(void *j){
  atomic_store_explicit(&x, 2, memory_order_seq_cst);
}

void *handler_func(void *i){ 
  qthread_exec();
  return 0;
}

int main(){
  pthread_t t;
  qthread_create(&handler, &handler_func, NULL);
  qthread_start(handler);
  for (int j = 0; j < N; j++){
    qthread_post_event(handler, &mes, NULL);
  }
}
