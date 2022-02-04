#include<stdio.h>
#include<stdatomic.h>
#include<pthread.h>
#include"qthread.h"

//1 trace
#ifndef N
#  warning "N was not defined"
#  define N 4
#endif

atomic_int g1,g2;
qthread_t handler;
void *mes1(void *j){
  atomic_int a = atomic_load_explicit(&g1, memory_order_seq_cst);
  return 0;
}

void *mes2(void *j){
  atomic_int b = atomic_load_explicit(&g2, memory_order_seq_cst);
  return 0;
}

void *th_post1(void *i){
  qthread_post_event(handler, &mes1, i); 
  return 0;
}

void *th_post2(void *i){
  qthread_post_event(handler, &mes2, i); 
  return 0;
}
void *handler_func(void *i){ 
  qthread_exec();
  return 0;
}

int main() {
  pthread_t t[2*N];

  qthread_create(&handler, &handler_func, NULL);
  for (int i = 0; i < 2*N; i++){
    pthread_create(&t[i++], NULL, &th_post1, NULL);
    pthread_create(&t[i], NULL, &th_post2, NULL);
  }
  for (int i = 0; i < 2*N; i++){
    pthread_join(t[i], NULL);
  }
  qthread_start(handler);
  qthread_wait(handler, NULL);
  return 0;
}
