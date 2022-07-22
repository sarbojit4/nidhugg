// nidhuggc: -sc -event
#include <stdio.h>
#include <stdatomic.h>
#include <pthread.h>
#include <assert.h>
#include "qthread.h"

#ifndef N
#  warning "N was not defined"
#  define N 4
#endif

qthread_t handler;
atomic_int x = -1;

void mes(void *j){
  int i = (intptr_t)j;
  x = i*2+1;
  assert(x == i*2+1);
}
void mespost(void *j){
  int i = (intptr_t)j;
  x = i*2;
  qthread_post_event(handler, &mes, j);
  assert(x == i*2);
}
void *th_post(void *i){
  qthread_post_event(handler, &mespost, i); 
  return NULL;
}

void *handler_func(void *i){ 
  qthread_exec();
  return NULL;
}

int main(){
  pthread_t t[N];
  qthread_create(&handler, &handler_func, NULL);
  qthread_start(handler);
  for (int i = 0; i < N; i++){
    pthread_create(&t[i], NULL, &th_post, (void*)(intptr_t)i);
  }
  for (int i = 0; i < N; i++){
    pthread_join(t[i], NULL);
  }
}
