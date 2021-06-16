#include <stdio.h>
#include <stdatomic.h>
#include <pthread.h>
#include "qthread.h"

//11 traces

qthread_t handler;

atomic_int x;
atomic_int y;
void *mes(void *j){
  atomic_store_explicit(&x, 2, memory_order_seq_cst);
  return 0;
}

void *th_post1(void *i){
  qthread_post_event(handler, &mes, i);
  atomic_store_explicit(&x, 2, memory_order_seq_cst);
  return 0;
}
void *th_post2(void *i){
  atomic_int a = atomic_load_explicit(&x, memory_order_seq_cst);
  qthread_post_event(handler, &mes, i);
  return 0;
}

void *handler_func(void *i){ 
  int quit = qthread_exec();
  return 0;
}

int main(){
  pthread_t t[2];
  qthread_create(&handler, &handler_func, NULL);
  qthread_start(handler);
  int i = 1;
  pthread_create(&t[0], NULL, &th_post1, &i);
  pthread_create(&t[1], NULL, &th_post2, &i);
  pthread_join(t[0], NULL);
  pthread_join(t[1], NULL);
  qthread_wait(handler, NULL);
}
