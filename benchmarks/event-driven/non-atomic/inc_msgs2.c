#include <stdio.h>
#include <stdatomic.h>
#include <pthread.h>
#include "qthread.h"

//6 traces

qthread_t handler;

atomic_int x;
atomic_int y;
atomic_int z;
//wx,ry,wz
void *m1(void *j){
  atomic_store_explicit(&x, 1, memory_order_seq_cst);
  atomic_int a = atomic_load_explicit(&y, memory_order_seq_cst);
  atomic_store_explicit(&z, 1, memory_order_seq_cst);
  return 0;
}
//wz,ry,wx
void *m2(void *j){
  atomic_store_explicit(&z, 2, memory_order_seq_cst);
  atomic_int a = atomic_load_explicit(&y, memory_order_seq_cst);
  atomic_store_explicit(&x, 2, memory_order_seq_cst);
  return 0;
}
//ry,wx,rz
void *m3(void *j){
  atomic_int a = atomic_load_explicit(&y, memory_order_seq_cst);
  atomic_store_explicit(&x, 3, memory_order_seq_cst);
  atomic_int b = atomic_load_explicit(&z, memory_order_seq_cst);
  return 0;
}

void *th_post1(void *i){
  qthread_post_event(handler, &m1, i); 
  return 0;
}
void *th_post2(void *i){
  qthread_post_event(handler, &m2, i); 
  return 0;
}
void *th_post3(void *i){
  qthread_post_event(handler, &m3, i); 
  return 0;
}

void *handler_func(void *i){ 
  int quit = qthread_exec();
  return 0;
}

int main(){
  qthread_create(&handler, &handler_func, NULL);
  qthread_start(handler);
  pthread_t t[3];
  pthread_create(&t[0], NULL, &th_post1, 0);
  pthread_create(&t[1], NULL, &th_post2, 0);
  pthread_create(&t[2], NULL, &th_post3, 0);
  pthread_join(t[0], NULL);
  pthread_join(t[1], NULL);
  pthread_join(t[2], NULL);
  qthread_wait(handler, NULL);
}
