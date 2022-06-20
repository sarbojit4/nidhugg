#include <stdio.h>
#include <stdatomic.h>
#include <pthread.h>
#include "qthread.h"

// (N+1)! traces

#ifndef N
#  warning "N was not defined; defining it as 2"
#  define N 4
#endif

qthread_t handler;
atomic_int x,y;

void mes(void *j){
  atomic_store_explicit(&x, 2, memory_order_seq_cst);
  atomic_store_explicit(&y, 2, memory_order_seq_cst);
}

void *th_post(void *i){
  qthread_post_event(handler, &mes, i); 
  return 0;
}

void *func(void *i){
  atomic_store_explicit(&x, 1, memory_order_seq_cst);
  return 0;
}

void *handler_func(void *i){ 
  qthread_exec();
  return 0;
}

int main(){
  pthread_t t[N+1];

  qthread_create(&handler, &handler_func, NULL);
  qthread_start(handler);
  pthread_create(&t[N], NULL, &func, NULL);
  for (int i = 0; i < N; i++){
    pthread_create(&t[i], NULL, &th_post, NULL);
  }
  for (int i = 0; i < N; i++){
    pthread_join(t[i], NULL);
  }
  pthread_join(t[N], NULL);
}
