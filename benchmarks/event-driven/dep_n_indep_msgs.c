#include<stdio.h>
#include<stdatomic.h>
#include<pthread.h>
#include"qthread.h"

#ifndef N
#  warning "N was not defined"
#  define N 5
#endif

atomic_int g;
void *mes1(void *j){
  atomic_store_explicit(&g, *(atomic_int *)j, memory_order_seq_cst);
  return 0;
}

void *mes2(void *j){
  return 0;
}

void *th_post1(void *i){
  qthread_post_event(1, &mes1, i); 
  return 0;
}

void *th_post2(void *i){
  qthread_post_event(1, &mes2, i); 
  return 0;
}
void *handler_func(void *i){ 
  qthread_exec();
  return 0;
}

int main() {
  pthread_t t[2*N];
  qthread_t handler;
  int a[2*N];
  qthread_create(&handler, &handler_func, NULL);
  for (int i = 0; i < 2*N; i++){
    a[i] = i+1;
    pthread_create(&t[i], NULL, &th_post1, &a[i]);
    i++;
    a[i] = i+1;
    pthread_create(&t[i], NULL, &th_post2, &a[i]);
  }
  for (int i = 0; i < 2*N; i++){
    pthread_join(t[i], NULL);
  }
  qthread_start(handler);
  qthread_quit(handler);
  qthread_wait(handler, NULL);
  return 0;
}
