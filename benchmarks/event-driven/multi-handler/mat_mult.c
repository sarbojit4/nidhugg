#include <stdio.h>
#include <stdatomic.h>
#include <pthread.h>
#include "qthread.h"


#ifndef M
#  warning "M was not defined; defining it as 3"
#  define M 4
#endif
#ifndef N
#  warning "N was not defined; defining it as 3"
#  define N 3
#endif
#ifndef K
#  warning "K was not defined; defining it as 2"
#  define K 5
#endif

typedef struct int_pair{
  int i;
  int j;
} int_pair;

qthread_t handler[N];
atomic_int A[M][K], B[K][N], C[M][N];

atomic_int x,y;
void mes(void *p){
  int i = (*(int_pair *)p).i;
  int j = (*(int_pair *)p).j;
  int elem = 0;
  for(int l = 0; l < K; l++){
    elem+=A[i][l]*B[l][j];
  }
  atomic_store_explicit(&C[i][j], elem, memory_order_seq_cst);
  return 0;
}

void *th_post(void *p){
  qthread_post_event(handler[(*(int_pair *)p).j], &mes, p); 
  return 0;
}

void *handler_func(void *i){ 
  int quit = qthread_exec();
  return 0;
}

int main(){
  for (int i = 0; i < M; i++){
    for (int j = 0; j < K; j++){
      A[i][j] = 1;
      //printf("%d ",A[i][j]);
    }
  }
  for (int i = 0; i < K; i++){
    for (int j = 0; j < N; j++){
      B[i][j] = 1;
      //printf("%d ",B[i][j]);
    }
  }
  for (int i = 0; i < N; i++){
    qthread_create(&handler[i], &handler_func, NULL);
    qthread_start(handler[i]);
  }

  pthread_t t[M][N];
  int_pair p[M][N];
  for (int i = 0; i < M; i++){
    for (int j = 0; j < N; j++){
      p[i][j].i=i;
      p[i][j].j=j;
      pthread_create(&t[i][j], NULL, &th_post, &p[i][j]);
    }
  }
  for (int i = 0; i < M; i++){
    for (int j = 0; j < N; j++){
      pthread_join(t[i][j], NULL);
    }
  }
  for (int i = 0; i < N; i++){
    qthread_wait(handler[i], NULL);
  }
  for (int i = 0; i < K; i++){
    for (int j = 0; j < N; j++){
      //printf("%d ",C[i][j]);
    }
  }
}
