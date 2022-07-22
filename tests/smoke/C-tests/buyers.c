// nidhuggc: -sc -event
#include <stdio.h>
#include <stdatomic.h>
#include <pthread.h>
#include <stdlib.h>
#include "qthread.h"

//N! traces
#ifndef N
#  warning "N was not defined; defining it as 5"
#  define N 5
#endif

qthread_t handler;
atomic_int price=50;
atomic_int contrib[N];
atomic_int id[N];
atomic_int state = 1; 

void __VERIFIER_assume(int truth);

atomic_int rand_int(){
  state = (state * 17);
  return state%10;
}
void bid(void *_id){
  atomic_int id = *((atomic_int *)_id);
  __VERIFIER_assume(price > 0);
  contrib[id]=rand_int();
  price -= contrib[id];
}

void *handler_func(void *i){ 
  qthread_exec();
  return 0;
}

int main(){
  state = 123;
  qthread_create(&handler, &handler_func, NULL);
  qthread_start(handler);
  for (int i = 0; i< N; i++){
    id[i]=i;
    contrib[i]=0;
    qthread_post_event(handler, &bid, &id[i]);
  }
}
