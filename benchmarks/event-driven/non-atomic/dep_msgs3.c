#include<stdio.h>
#include<stdatomic.h>
#include<pthread.h>
#include"qthread.h"

//(((2*N)!)^2)/2

#ifndef N
#  warning "N was not defined"
#  define N 2
#endif

atomic_int g1,g2;
void *mes1(void *j){
  atomic_store_explicit(&g1, *(atomic_int *)j, memory_order_seq_cst);
  return 0;
}

void *mes2(void *j){
  atomic_store_explicit(&g2, *(atomic_int *)j, memory_order_seq_cst);
  return 0;
}
void *mes3(void *j){
  atomic_store_explicit(&g1, *(atomic_int *)j, memory_order_seq_cst);
  atomic_store_explicit(&g2, *(atomic_int *)j, memory_order_seq_cst);
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
void *th_post3(void *i){
  qthread_post_event(1, &mes3, i); 
  return 0;
}
void *handler_func(void *i){ 
  qthread_exec();
  return 0;
}

int main() {
  pthread_t t[3*N];
  qthread_t handler;
  int a[3*N];
  qthread_create(&handler, &handler_func, NULL);
  for (int i = 0; i < 3*N; i++){
    a[i] = i+1;
    pthread_create(&t[i], NULL, &th_post1, &a[i]);
    i++;
    a[i] = i+1;
    pthread_create(&t[i], NULL, &th_post2, &a[i]);
    i++;
    a[i] = i+1;
    pthread_create(&t[i], NULL, &th_post3, &a[i]);
  }
  for (int i = 0; i < 3*N; i++){
    pthread_join(t[i], NULL);
  }
  qthread_start(handler);
  qthread_quit(handler);
  qthread_wait(handler, NULL);
  return 0;
}
