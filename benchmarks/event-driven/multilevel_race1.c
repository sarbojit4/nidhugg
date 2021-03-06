#include <stdio.h>
#include <stdatomic.h>
#include <pthread.h>
#include "qthread.h"

//N!*N! traces
#ifndef N
#  warning "N was not defined; defining it as 2"
#  define N 3
#endif

qthread_t handler;

atomic_int x;
atomic_int y;
void *mes(void *j){
  atomic_store_explicit(&x, 2, memory_order_seq_cst);
  return 0;
}

void *mespost(void *j){
  qthread_post_event(handler, &mes, j); 
  atomic_store_explicit(&y, 2, memory_order_seq_cst);
  return 0;
}
void *th_post(void *i){
  qthread_post_event(handler, &mespost, i); 
  return 0;
}

void *handler_func(void *i){ 
  int quit = qthread_exec();
  return 0;
}

int main(){
  pthread_t t[N];
  int a[N];
  qthread_create(&handler, &handler_func, NULL);
  qthread_start(handler);
  for (int i = 0; i < N; i++){
    a[i] = i+1;
    pthread_create(&t[i], NULL, &th_post, &a[i]);
  }
  for (int i = 0; i < N; i++){
    pthread_join(t[i], NULL);
  }
  qthread_wait(handler, NULL);
}
