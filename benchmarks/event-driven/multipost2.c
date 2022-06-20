#include <stdio.h>
#include <stdatomic.h>
#include <pthread.h>
#include "qthread.h"

//((N+1)^N)*N! traces

#ifndef N
#  warning "N was not defined"
#  define N 3
#endif

qthread_t handler;
atomic_int x;
int a[2*N];

void mes1(void *j){
  atomic_store_explicit(&x, 2, memory_order_seq_cst);
}

void mes2(void *j){
  atomic_int a = atomic_load_explicit(&x, memory_order_seq_cst);
}

void mespost(void *j){
  int a = *(int *)j;
  if(a%2 == 1) qthread_post_event(handler, &mes1, j); 
  if(a%2 == 0) qthread_post_event(handler, &mes2, j); 
}

void *th_post(void *i){
  qthread_post_event(handler, &mespost, i); 
  return 0;
}

void *handler_func(void *i){ 
  qthread_exec();
  return 0;
}

int main(){
  pthread_t t[2*N];
  qthread_create(&handler, &handler_func, NULL);
  qthread_start(handler);
  for (int i = 0; i < 2*N; i++) a[i] = i+1;
  for (int i = 0; i < 2*N; i++){
    pthread_create(&t[i], NULL, &th_post, &a[i]);
  }
  for (int i = 0; i < 2*N; i++){
    pthread_join(t[i], NULL);
  }
}
