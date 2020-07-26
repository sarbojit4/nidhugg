#include <stdio.h>
#include <stdatomic.h>
#include <pthread.h>
#include "qthread.h"

atomic_int x;
void *message(void *j){
  return 0;
}

void *thread(void *i){
  qthread_post_event(1, &message, i); 
  return 0;
}

void *handler_func(void *i){ 
  int quit = qthread_exec();
  return i;
}

int main(){
  qthread_t handler;
  pthread_t tid1, tid2;
  int a = 2;
  qthread_create(&handler, &handler_func, &a);
  pthread_create(&tid1, NULL, &thread, &tid1);
  pthread_create(&tid2, NULL, &thread, &tid2);
  pthread_join(tid1, NULL);
  pthread_join(tid2, NULL);
  qthread_start(handler);
  qthread_wait(handler, NULL);
}
