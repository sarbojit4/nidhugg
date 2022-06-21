#include <stdio.h>
#include <stdatomic.h>
#include <pthread.h>
#include "qthread.h"

#ifndef N
#  warning "N was not defined; defining it as 2"
#  define N 3
#endif

typedef struct {
  int i;
  int j;
} param;

qthread_t collectors[N];

atomic_int decision[N];
atomic_int value[N];
param p[N][N];
atomic_int a[N];

void send_value(void *par) {
  atomic_int val = atomic_load_explicit(&value[(*(param *)par).j], memory_order_seq_cst);
  if (val > decision[(*(param *)par).i]) {
    decision[(*(param *)par).i] = val;
  }
}

void *handler_func(void *j){ 
  atomic_store_explicit(&value[*(atomic_int *)j], *(atomic_int *)j, memory_order_seq_cst);
  
  for (int i = 0; i < N; i++) {
    int k = *(int *)j;
    p[i][k].i = i;
    p[i][k].j = k;
    qthread_post_event(collectors[i], &send_value, &p[i][k]);
  }
  int quit = qthread_exec();
  return 0;
}

int main() {
  for (int i = 0; i < N; i++) {
    decision[i] = -1;
  }

  for (int i = 0; i < N; i++) {
    a[i] = i;
    qthread_create(&collectors[i], &handler_func, &a[i]);
    qthread_start(collectors[i]);
  }
 
  for (int i = 0; i < N; i++) {
    qthread_wait(collectors[i], NULL);
  }
}
