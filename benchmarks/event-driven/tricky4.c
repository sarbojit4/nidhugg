#include <stdio.h>
#include <stdatomic.h>
#include <pthread.h>
#include "qthread.h"

// 24 traces

qthread_t handler1;

atomic_int x,y,z;
void *mes2(void *j){
  atomic_int a = atomic_load_explicit(&x, memory_order_seq_cst);
  atomic_store_explicit(&y, 2, memory_order_seq_cst);
  return 0;
}

void *th_post1(void *i){
  atomic_store_explicit(&y, 2, memory_order_seq_cst);
  return 0;
}

void *th_post2(void *i){
  qthread_post_event(handler1, &mes2, i); 
  return 0;
}

void *handler_func(void *i){ 
  int quit = qthread_exec();
  return 0;
}

int main(){
  pthread_t t[4];

  qthread_create(&handler1, &handler_func, NULL);
  qthread_start(handler1);
  pthread_create(&t[0], NULL, &th_post1, NULL);
  pthread_create(&t[1], NULL, &th_post1, NULL);
  pthread_create(&t[2], NULL, &th_post2, NULL);
  pthread_create(&t[3], NULL, &th_post2, NULL);
  pthread_join(t[0], NULL);
  pthread_join(t[1], NULL);
  pthread_join(t[2], NULL);
  pthread_join(t[3], NULL);
  qthread_wait(handler1, NULL);
}
