#include <stdio.h>
#include <stdatomic.h>
#include <pthread.h>
#include "qthread.h"

//12 traces
qthread_t handler;
atomic_int x,y;

void m1(void *j){
  atomic_store_explicit(&x, 1, memory_order_seq_cst);
}

void m2(void *j){
  atomic_store_explicit(&x, 2, memory_order_seq_cst);
}

void m3(void *j){
  atomic_store_explicit(&y, 1, memory_order_seq_cst);
  atomic_store_explicit(&x, 3, memory_order_seq_cst);
}

void *t1(void *i){
  qthread_post_event(handler, &m1, i); 
  return 0;
}
void *t2(void *i){
  qthread_post_event(handler, &m2, i); 
  return 0;
}
void *t3(void *i){
  qthread_post_event(handler, &m3, i); 
  return 0;
}

void *t4(void *i){
  atomic_store_explicit(&y, 2, memory_order_seq_cst);
  return 0;
}

void *handler_func(void *i){ 
  qthread_exec();
  return 0;
}

int main(){
  pthread_t t[4];
  qthread_create(&handler, &handler_func, NULL);
  qthread_start(handler);
  pthread_create(&t[0], NULL, &t1, NULL);
  pthread_create(&t[1], NULL, &t2, NULL);
  pthread_create(&t[2], NULL, &t3, NULL);
  for (int i = 0; i < 3; i++){
    pthread_join(t[i], NULL);
  }
  pthread_create(&t[3], NULL, &t4, NULL);
  pthread_join(t[3], NULL);
}
