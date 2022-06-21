#include <stdio.h>
#include <stdatomic.h>
#include <pthread.h>
#include "qthread.h"

//((N+1)^N)*(N!) traces
#ifndef N
#  warning "N was not defined; defining it as 3"
#  define N 3
#endif

qthread_t handler1;
qthread_t handler2;
atomic_int x;

void mes1(void *j){
  atomic_store_explicit(&x, 2, memory_order_seq_cst);
}

void mes2(void *j){
  atomic_int a = atomic_load_explicit(&x, memory_order_seq_cst);
}

void *th_post1(void *i){
  qthread_post_event(handler1, &mes1, i); 
  return 0;
}

void *th_post2(void *i){
  qthread_post_event(handler2, &mes2, i); 
  return 0;
}

void *handler_func(void *i){ 
  qthread_exec();
  return 0;
}

int main(){
  pthread_t t1[N],t2[N];

  qthread_create(&handler1, &handler_func, NULL);
  qthread_start(handler1);
  qthread_create(&handler2, &handler_func, NULL);
  qthread_start(handler2);
  for (int i = 0; i < N; i++){
    pthread_create(&t1[i], NULL, &th_post1, NULL);
  }
  for (int i = 0; i < N; i++){
    pthread_create(&t2[i], NULL, &th_post2, NULL);
  }
  for (int i = 0; i < N; i++){
    pthread_join(t1[i], NULL);
  }
  pthread_join(t2[0], NULL);
}
