#include<stdio.h>
#include<stdatomic.h>
#include<pthread.h>
#include"qthread.h"
//[((N+1)^N)*(N!)]^2 traces
#ifndef N
#  warning "N was not defined"
#  define N 2
#endif

atomic_int g1,g2;
qthread_t handler;

void *mes1(void *j){
  atomic_store_explicit(&g1, 1, memory_order_seq_cst);
  return 0;
}

void *mes2(void *j){
  atomic_store_explicit(&g2, 1, memory_order_seq_cst);
  return 0;
}
void *mes3(void *j){
  atomic_int a = atomic_load_explicit(&g1, memory_order_seq_cst);
  return 0;
}
void *mes4(void *j){
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
void *th_post3(void *i){
  qthread_post_event(handler, &mes3, i); 
  return 0;
}
void *th_post4(void *i){
  qthread_post_event(handler, &mes4, i); 
  return 0;
}
void *handler_func(void *i){ 
  qthread_exec();
  return 0;
}

int main() {
  pthread_t t[4*N];
  int a[4*N];
  qthread_create(&handler, &handler_func, NULL);
  for (int i = 0; i < 4*N; i++){
    a[i] = i+1;
    pthread_create(&t[i], NULL, &th_post1, &a[i]);
    i++;
    a[i] = i+1;
    pthread_create(&t[i], NULL, &th_post2, &a[i]);
    i++;
    a[i] = i+1;
    pthread_create(&t[i], NULL, &th_post3, &a[i]);
    i++;
    a[i] = i+1;
    pthread_create(&t[i], NULL, &th_post4, &a[i]);
  }
  for (int i = 0; i < 4*N; i++){
    pthread_join(t[i], NULL);
  }
  qthread_start(handler);
  qthread_wait(handler, NULL);
  return 0;
}
