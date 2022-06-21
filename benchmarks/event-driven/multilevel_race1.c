#include <stdio.h>
#include <stdatomic.h>
#include <pthread.h>
#include "qthread.h"

#ifndef N
#  warning "N was not defined"
#  define N 4
#endif

qthread_t handler;
atomic_int x;
atomic_int y;

void mes(void *j){
  atomic_store_explicit(&x, 2, memory_order_seq_cst);
}
void mes1(void *j){
  atomic_store_explicit(&x, 2, memory_order_seq_cst);
}
void mespost(void *j){
  atomic_store_explicit(&x, 2, memory_order_seq_cst);
  qthread_post_event(handler, &mes, j); 
}
void mespost1(void *j){
  atomic_store_explicit(&x, 2, memory_order_seq_cst);
  qthread_post_event(handler, &mes1, j); 
}
void *th_post(void *i){
  qthread_post_event(handler, &mespost, i); 
  return 0;
}
void *th_post1(void *i){
  qthread_post_event(handler, &mespost1, i); 
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
  for (int i = 0; i < N-1; i++){
    pthread_create(&t[i], NULL, &th_post, NULL);
  }
  pthread_create(&t[N-1], NULL, &th_post1, NULL);
  for (int i = 0; i < N-1; i++){
    pthread_join(t[i], NULL);
  }
}
