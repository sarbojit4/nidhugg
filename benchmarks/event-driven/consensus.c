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

void *send_value(void *par) {
  atomic_int val = atomic_load_explicit(&value[(*(param *)par).j], memory_order_seq_cst);
  if (val > decision[(*(param *)par).i]) {
    decision[(*(param *)par).i] = val;
  }
  return 0;
}

void *broadcast(void *j) {
  atomic_store_explicit(&value[*(atomic_int *)j], *(atomic_int *)j, memory_order_seq_cst);
  
  for (int i = 0; i < N; i++) {
    param p;
    p.i = i;
    p.j = *(int *)j;
    qthread_post_event(collectors[i], &send_value, &p);
  }
  return 0;
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
  atomic_int a[N];
  
  for (int i = 0; i < N; i++) {
    a[i] = i;
    pthread_create(&t[i], NULL, &broadcast, &a[i]);
  }
  
  for (int i = 0; i < N; i++) {
    pthread_join(t[i], NULL);
  }
  
  for (int i = 0; i < N; i++) {
    qthread_wait(collectors[i], NULL);
  }
}
