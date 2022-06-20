#include<stdio.h>
#include<stdatomic.h>
#include<pthread.h>
#include"qthread.h"

//N!*N! traces

#ifndef N
#  warning "N was not defined"
#  define N 4
#endif

atomic_int g1,g2;
qthread_t handler;

void mes1(void *j){
  atomic_store_explicit(&g1, 2, memory_order_seq_cst);
}

void mes2(void *j){
  atomic_store_explicit(&g2, 2, memory_order_seq_cst);
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
    pthread_create(&t[i], NULL, &th_post1, NULL);
    i++;
    pthread_create(&t[i], NULL, &th_post2, NULL);
  }
  for (int i = 0; i < 2*N; i++){
    pthread_join(t[i], NULL);
  }
  qthread_start(handler);
  return 0;
}
