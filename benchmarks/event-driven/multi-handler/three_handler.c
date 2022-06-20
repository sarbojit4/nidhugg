#include <stdio.h>
#include <stdatomic.h>
#include <pthread.h>
#include "qthread.h"

// 24 traces

qthread_t handler1,handler2,handler3;
atomic_int x,y,z,u,v;

void mes1(void *j){
  atomic_store_explicit(&x, 2, memory_order_seq_cst);
}

void mes2(void *j){
  atomic_store_explicit(&z, 2, memory_order_seq_cst);
  atomic_store_explicit(&x, 2, memory_order_seq_cst);
}

void mes3(void *j){
  atomic_store_explicit(&y, 2, memory_order_seq_cst);
  atomic_store_explicit(&x, 2, memory_order_seq_cst);
}

void mes4(void *j){
  atomic_int a = atomic_load_explicit(&y, memory_order_seq_cst);
  atomic_int b = atomic_load_explicit(&u, memory_order_seq_cst);
}

void mes5(void *j){
  atomic_int a = atomic_load_explicit(&z, memory_order_seq_cst);
  atomic_store_explicit(&v, 2, memory_order_seq_cst);
}

void *handler_func(void *i){ 
  int quit = qthread_exec();
  return 0;
}

int main(){
  pthread_t t[7];

  qthread_create(&handler1, &handler_func, NULL);
  qthread_start(handler1);
  qthread_create(&handler2, &handler_func, NULL);
  qthread_start(handler2);
  qthread_create(&handler3, &handler_func, NULL);
  qthread_start(handler3);

  qthread_post_event(handler1, &mes1, NULL);
  qthread_post_event(handler2, &mes2, NULL);
  qthread_post_event(handler3, &mes3, NULL);
  qthread_post_event(handler2, &mes4, NULL);
  qthread_post_event(handler3, &mes5, NULL);
}
