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
atomic_int a[(N+1)*N];
atomic_int count[(N+1)*N];
atomic_int id[N];

void __VERIFIER_assume(intptr_t);

void mes(void *_id){
  atomic_int num = *(atomic_int *)_id;
  for (atomic_int i = num*N; i < N+num*N; i++){
    atomic_store_explicit(&a[i], 2, memory_order_seq_cst);
  }
  for (atomic_int i = N+num*N; i < 2*N+num*N; i++){
    atomic_int b = atomic_load_explicit(&a[i], memory_order_seq_cst);
  }
  id[N-1] = 0;
}

void *handler_func(void *i){ 
  qthread_exec();
  return 0;
}

int main(){
  qthread_create(&handler, &handler_func, NULL);
  qthread_start(handler);
  for (int i = 0; i < N; i++){
    id[i] = i;
    qthread_post_event(handler, &mes, &id[i]); 
  }
}
