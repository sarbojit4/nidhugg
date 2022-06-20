#include <stdio.h>
#include <stdatomic.h>
#include <pthread.h>
#include "qthread.h"

//1 trace
#ifndef N
#  warning "N was not defined"
#  define N 7
#endif

qthread_t handler;
atomic_int x;

void mes(void *j){
  atomic_int a = atomic_load_explicit(&x, memory_order_seq_cst);
}

void *th_post(void *i){
  qthread_post_event(handler, &mes, i); 
  return 0;
}

void *handler_func(void *i){ 
  qthread_exec();
  return 0;
}

int main(){
  pthread_t t[N];
  qthread_create(&handler, &handler_func, NULL);
  qthread_start(handler);
  for (int i = 0; i < N; i++){
    pthread_create(&t[i], NULL, &th_post, NULL);
  }
  for (int i = 0; i < N; i++){
    pthread_join(t[i], NULL);
  }
}
