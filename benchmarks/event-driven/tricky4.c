#include <stdio.h>
#include <stdatomic.h>
#include <pthread.h>
#include "qthread.h"

// 24 traces

qthread_t handler;
atomic_int x,y;

void mes(void *j){
  atomic_int a = atomic_load_explicit(&x, memory_order_seq_cst);
  atomic_store_explicit(&y, 2, memory_order_seq_cst);
}

void *thread_func(void *i){
  atomic_store_explicit(&y, 2, memory_order_seq_cst);
  return 0;
}

void *th_post(void *i){
  qthread_post_event(handler, &mes, i); 
  return 0;
}

void *handler_func(void *i){ 
  int quit = qthread_exec();
  return 0;
}

int main(){
  pthread_t t[4];

  qthread_create(&handler, &handler_func, NULL);
  qthread_start(handler);
  pthread_create(&t[0], NULL, &thread_func, NULL);
  pthread_create(&t[1], NULL, &thread_func, NULL);
  pthread_create(&t[2], NULL, &th_post, NULL);
  pthread_create(&t[3], NULL, &th_post, NULL);
  pthread_join(t[0], NULL);
  pthread_join(t[1], NULL);
  pthread_join(t[2], NULL);
  pthread_join(t[3], NULL);
}
