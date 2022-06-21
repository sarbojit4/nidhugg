#include <stdio.h>
#include <stdatomic.h>
#include <pthread.h>
#include "qthread.h"

//2 traces

qthread_t handler;
atomic_int x,y;

void mes1(void *j){
  atomic_int a = atomic_load_explicit(&y, memory_order_seq_cst);
  if(a == 0){
    atomic_store_explicit(&x, 1, memory_order_seq_cst);
  }
}
void mes2(void *j){
  atomic_store_explicit(&x, 2, memory_order_seq_cst);
}

void *th_post1(void *i){
  qthread_post_event(handler, &mes1, i); 
  return 0;
}
void *th_post2(void *i){
  atomic_store_explicit(&y, 1, memory_order_seq_cst);
  qthread_post_event(handler, &mes2, i); 
  return 0;
}
void *handler_func(void *i){ 
  qthread_exec();
  return 0;
}
int main(){
  pthread_t t[2];

  qthread_create(&handler, &handler_func, NULL);
  qthread_start(handler);
  pthread_create(&t[0], NULL, &th_post1, NULL);
  pthread_create(&t[1], NULL, &th_post2, NULL);
  pthread_join(t[0], NULL);
  pthread_join(t[1], NULL);
}
