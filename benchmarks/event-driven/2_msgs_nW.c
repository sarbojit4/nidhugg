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
atomic_int a[N];

void __VERIFIER_assume(intptr_t);

void mes(void *_id){
  for (atomic_int i = 0; i < N; i++){
    atomic_store_explicit(&a[i], 2, memory_order_seq_cst);
  }
}

void *handler_func(void *i){ 
  qthread_exec();
  return 0;
}

int main(){
  qthread_create(&handler, &handler_func, NULL);
  qthread_start(handler);
  //for (int i = 0; i < N; i++){
    qthread_post_event(handler, &mes, NULL); 
    qthread_post_event(handler, &mes, NULL); 
  //}
}