#include<stdio.h>
#include<stdatomic.h>
#include<pthread.h>
#include"qthread.h"

// 1 trace and N!*N!-1 assume blocked traces
#ifndef N
#  warning "N was not defined; defining it as 3"
#  define N 3
#endif

atomic_int last_ping_msg;
atomic_int last_pong_msg;
qthread_t ping, pong;
atomic_int msg[N];

void __VERIFIER_assume(int truth);

void pong_msg(void *msg_ptr){
  atomic_int this_msg = *((atomic_int *)msg_ptr);
  __VERIFIER_assume(last_pong_msg < this_msg);
  atomic_store_explicit(&last_pong_msg, this_msg, memory_order_seq_cst);
}

void ping_msg(void *msg_ptr){
  atomic_int this_msg = *((atomic_int *)msg_ptr);
  __VERIFIER_assume(last_ping_msg < this_msg);
  atomic_store_explicit(&last_ping_msg, this_msg, memory_order_seq_cst);
  qthread_post_event(ping, &pong_msg, msg_ptr);
}

void *pong_func(void *i){
  qthread_exec();
  return NULL;
}

void *init(void *i){
  for (int i = 0; i < N; i++){
    msg[i] = i;
    qthread_post_event(pong, &ping_msg, &msg[i]);
  }
  return NULL;
}

void *ping_func(void *i){
  qthread_exec();
  return 0;
}

int main() {
  last_ping_msg = -1;
  last_pong_msg = -1;
  qthread_create(&ping, &ping_func, NULL);
  qthread_create(&pong, &pong_func, NULL);
  qthread_start(ping);
  qthread_start(pong);
  pthread_t t;
  pthread_create(&t, NULL, &init, NULL);
  pthread_join(t,NULL);
  return 0;
}
