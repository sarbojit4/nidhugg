#include <stdio.h>
#include <stdatomic.h>
#include <pthread.h>
#include "qthread.h"

//2 traces

qthread_t handler;

atomic_int x;
atomic_int y;
void *m1(void *j){
  atomic_int a = atomic_load_explicit(&y, memory_order_seq_cst);
  if(a == 0){
    atomic_store_explicit(&x, 1, memory_order_seq_cst);
  }
  return 0;
}
void *m2(void *j){
  atomic_store_explicit(&x, 2, memory_order_seq_cst);
  return 0;
}

void *p(void *i){
  qthread_post_event(handler, &m1, i); 
  return 0;
}
void *q(void *i){
  atomic_store_explicit(&y, 1, memory_order_seq_cst);
  qthread_post_event(handler, &m2, i); 
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
  pthread_create(&t[0], NULL, &p, 0);
  pthread_create(&t[1], NULL, &q, 0);
  pthread_join(t[0], NULL);
  pthread_join(t[1], NULL);
  qthread_wait(handler, NULL);
}
