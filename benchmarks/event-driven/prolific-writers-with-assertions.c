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
atomic_int a[N*N];
atomic_int counter[N*N];
atomic_int id[N];
atomic_int msg_finished[N];

void __VERIFIER_assume(intptr_t);

void mes(void *_id){
  atomic_int num = *(atomic_int *)_id;
  for (atomic_int i = num*N; i <= (N+num*N-1)%(N*N); i++){
    atomic_store_explicit(&a[i], 2, memory_order_seq_cst);
    atomic_store_explicit(&counter[i], counter[i]+1, memory_order_seq_cst);
  }
  for (atomic_int i = (N+num*N)%(N*N); i <= (2*N+num*N-1)%(N*N); i++){
    atomic_int b = atomic_load_explicit(&a[i], memory_order_seq_cst);
    atomic_store_explicit(&counter[i], counter[i]+1, memory_order_seq_cst);
  }
  msg_finished[num] = 1;
  for (atomic_int i = (N+num*N)%(N*N); i <= (2*N+num*N-1)%(N*N); i++)
    assert(msg_finished[num] == 0 || msg_finished[(num+1)%N] == 0 || counter[i] == 2);
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
    msg_finished[i] = 0;
  }
  for (int i = 0; i < N*N; i++) counter[i] = 0;
  for (int i = 0; i < N; i++){
    qthread_post_event(handler, &mes, &id[i]); 
  }
  //for(int i=0; i<N; i++) __VERIFIER_assume(msg_finished[i] == 1);
  //for(int i=0; i<N*N; i++) assert(counter[i] == 2);
}
