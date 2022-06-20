#include <stdio.h>
#include <stdatomic.h>
#include <pthread.h>
#include "qthread.h"

// 8 traces

qthread_t handler1;
qthread_t handler2;
atomic_int x,y,z;

void mes1(void *j){
  atomic_store_explicit(&x, 2, memory_order_seq_cst);
}

void mes2(void *j){
  atomic_store_explicit(&y, 2, memory_order_seq_cst);
  atomic_store_explicit(&x, 2, memory_order_seq_cst);
}
void mes3(void *j){
  atomic_int b = atomic_load_explicit(&z, memory_order_seq_cst);
  atomic_int a = atomic_load_explicit(&y, memory_order_seq_cst);
}

void *th_post1(void *i){
  qthread_post_event(handler1, &mes1, i); 
  return 0;
}

void *th_post2(void *i){
  qthread_post_event(handler1, &mes2, i); 
  return 0;
}

void *th_post3(void *i){
  qthread_post_event(handler2, &mes3, i); 
  return 0;
}

void *handler_func(void *i){ 
  qthread_exec();
  return 0;
}

int main(){
  pthread_t t[4];

  qthread_create(&handler1, &handler_func, NULL);
  qthread_start(handler1);
  qthread_create(&handler2, &handler_func, NULL);
  qthread_start(handler2);
  pthread_create(&t[0], NULL, &th_post1, NULL);
  pthread_create(&t[1], NULL, &th_post2, NULL);
  pthread_create(&t[2], NULL, &th_post3, NULL);
  pthread_create(&t[3], NULL, &th_post3, NULL);
  pthread_join(t[0], NULL);
  pthread_join(t[1], NULL);
  pthread_join(t[2], NULL);
  pthread_join(t[3], NULL);
}
