#include <stdio.h>
#include <stdatomic.h>
#include <pthread.h>
#include "qthread.h"

#ifndef N
#  warning "N was not defined; defining it as 2"
#  define N 2
#endif

typedef struct {
  int i;
  int j;
} param;

qthread_t collectors[N];

atomic_int decision[N];
atomic_int value[N];

atomic_int a = 0;

void *send_value(void *j) {
  param p = *(param *)j;
  atomic_int val = value[p.j];
  
  if (val > decision[p.i]) {
    decision[p.i] = val;
  }
}

void *broadcast(void *j) {
  atomic_store_explicit(&value[*(atomic_int *)j], *(atomic_int *)j, memory_order_seq_cst);
  
  for (int i = 0; i < N; i++) {
    param p;
    p.i = i;
    p.j = *(int *)j;
    qthread_post_event(collectors[i], &send_value, &p);
  }
}

void *handler_func(void *i){ 
  int quit = qthread_exec();
  
  return 0;
}

int main() {
  for (int i = 0; i < N; i++) {
    decision[i] = -1;
  }
  
  for (int i = 0; i < N; i++) {
    qthread_create(&collectors[i], &handler_func, NULL);
    qthread_start(collectors[i]);
  }
  
  pthread_t t[N];
  
  for (int i = 0; i < N; i++) {
    pthread_create(&t[i], NULL, &broadcast, i);
  }
  
  for (int i = 0; i < N; i++) {
    pthread_join(t[i], NULL);
  }
  
  for (int i = 0; i < N; i++) {
    qthread_wait(collectors[i], NULL);
  }
}
