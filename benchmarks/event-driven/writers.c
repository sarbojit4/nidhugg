#include <stdio.h>
#include <stdatomic.h>
#include <pthread.h>
#include <assert.h>
#include "qthread.h"

//N! traces
#ifndef N
#  warning "N was not defined; defining it as 5"
#  define N 5
#endif

qthread_t handler;
atomic_int x;

void __VERIFIER_assume(intptr_t);

void mes(void *j){
  atomic_store_explicit(&x, 2, memory_order_seq_cst);
  assert(x == 2);
}

void *th_post(void *i){
  qthread_post_event(handler, &mes, i); 
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
  for (int i = 0; i < N; i++){
    pthread_create(&t[i], NULL, &th_post, NULL);
  }
  for (int i = 0; i < N; i++){
    pthread_join(t[i], NULL);
  }
}
