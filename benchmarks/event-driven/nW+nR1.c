#include<stdio.h>
#include<stdatomic.h>
#include<pthread.h>
#include"qthread.h"
/* ((N+1)^(N-1))*(N!) traces*/
#ifndef N
#  warning "N was not defined"
#  define N 3
#endif

atomic_int g;
qthread_t handler;
void *mes1(void *j){
  atomic_store_explicit(&g, 1, memory_order_seq_cst);
  return 0;
}

void *mes2(void *j){
  atomic_int a = atomic_load_explicit(&g, memory_order_seq_cst);
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
  pthread_t t[2*N-1];

  qthread_create(&handler, &handler_func, NULL);
  qthread_start(handler);
  for (int i = 0; i < N; i++){
    pthread_create(&t[i], NULL, &th_post1, NULL);
  }
  for (int i = N; i < 2*N-1; i++){
    pthread_create(&t[i], NULL, &th_post2, NULL);
  }
  for (int i = 0; i < 2*N-1; i++){
    pthread_join(t[i], NULL);
  }
  qthread_wait(handler, NULL);
  return 0;
}
