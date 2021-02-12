#include <stdio.h>
#include <stdatomic.h>
#include <pthread.h>
#include "qthread.h"

//2 traces

qthread_t handler1,handler2;

atomic_int x;
void *m1(void *j){
  atomic_store_explicit(&x, 1, memory_order_seq_cst);
  return 0;
}

void *m3(void *j){
  atomic_int a = atomic_load_explicit(&x, memory_order_seq_cst);
  return 0;
}

void *m2(void *j){
  qthread_post_event(handler2, &m3, j);
  return 0;
}

void *th_post1(void *i){
  qthread_post_event(handler1, &m1, i); 
  return 0;
}
void *th_post2(void *i){
  qthread_post_event(handler1, &m2, i); 
  return 0;
}

void *handler_func(void *i){ 
  int quit = qthread_exec();
  return 0;
}

int main(){
  qthread_create(&handler1, &handler_func, NULL);
  qthread_create(&handler2, &handler_func, NULL);
  qthread_start(handler1);
  qthread_start(handler2);
  pthread_t t[2];
  pthread_create(&t[0], NULL, &th_post1, 0);
  pthread_create(&t[1], NULL, &th_post2, 0);
  pthread_join(t[0], NULL);
  pthread_join(t[1], NULL);
  qthread_wait(handler1, NULL);
  qthread_wait(handler2, NULL);
}
