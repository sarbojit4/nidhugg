#include <stdio.h>
#include <stdatomic.h>
#include <pthread.h>
#include <assert.h>
#include <math.h>
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
atomic_int p[N];
atomic_int msg_finished[N];
atomic_int sum_of_elems = 0;

atomic_int x,y;
void __VERIFIER_assume(intptr_t);

void sum_sum(void *arg){
  atomic_int i = atomic_load_explicit((atomic_int *)arg, memory_order_seq_cst);
  sum_of_elems += A[0][i];
  atomic_store_explicit(&msg_finished[i], 1, memory_order_seq_cst);
  p[i]=0;
} 
void sum_col_elems(void *arg){
  atomic_int i = atomic_load_explicit((atomic_int *)arg, memory_order_seq_cst);
  for(int j = 1; j < M; j++){
    A[0][i] += A[j][i];
  }
  qthread_post_event(handler2, &sum_sum, arg); 
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
      msg_finished[i] = 0;
      p[i] = i;
      qthread_post_event(handler1, &sum_col_elems, &p[i]); 
  }

  int expected_sum = (((M/2)+(M%2))*(N/2))+((M/2)*((N/2)+(N%2)));
  int all_finished = 1;
  for (int i = 0; i < N; i++){
    atomic_int finished = atomic_load_explicit(&msg_finished[i], memory_order_seq_cst);
    if(finished == 0){} //all_finished = 1
  }
  //if(all_finished == 1) assert(sum_of_elems == expected_sum);

}
