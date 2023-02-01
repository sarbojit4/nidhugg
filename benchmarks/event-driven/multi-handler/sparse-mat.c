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

qthread_t handler1, handler2;
atomic_int A[M][N];
int p[N];
atomic_int sum_of_elems = 0;

atomic_int x,y;
void sum_sum(void *p){
  int i = (*(int *)p);
  sum_of_elems += A[0][i];
} 
void sum_col_elems(void *p){
  int i = (*(int *)p);
  for(int j = 1; j < M; j++){
    A[0][j] += A[j][i];
  }
  qthread_post_event(handler1, &sum_sum, p); 
}


void *handler_func(void *i){ 
  int quit = qthread_exec();
  return 0;
}

int main(){
  for (int i = 0; i < M; i++){
    for (int j = 0; j < N; j++){
      A[i][j] = (i+j)%2;
    }
  }
  qthread_create(&handler1, &handler_func, NULL);
  qthread_start(handler1);
  qthread_create(&handler2, &handler_func, NULL);
  qthread_start(handler2);

  for (int i = 0; i < N; i++){
      p[i] = i;
      qthread_post_event(handler1, &sum_col_elems, &p[i]); 
  }
}
