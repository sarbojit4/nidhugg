#include <stdio.h>
#include <stdatomic.h>
#include <pthread.h>
#include <stdlib.h>
#include <assert.h>
#include "qthread.h"

//N! traces
#ifndef N
#  warning "N was not defined; defining it as 5"
#  define N 5
#endif

qthread_t coordinator;
atomic_int price=50;
atomic_int amount[N];
atomic_int contributed[N];
atomic_int id[N];
atomic_int state; 
atomic_int done_bidding[N];

void __VERIFIER_assume(int truth);

atomic_int rand_int(int i){
  return (state*i)%10;
}
void bid(void *_id){
  atomic_int i = *((atomic_int *)_id);
  if(price > 0){
    price -= amount[i];
    contributed[i] = 1;
  }
  done_bidding[i] = 1;
}

void *buyer_func(void *_id){
  atomic_int i = *((atomic_int *)_id);
  amount[i]=rand_int(i);
  qthread_post_event(coordinator, &bid, &id[i]);
  return NULL;
}

void *coordinator_func(void *i){ 
  qthread_exec();
  return 0;
}

int main(){
  int p = price;
  pthread_t buyer[N];
  state = 123;
  qthread_create(&coordinator, &coordinator_func, NULL);
  qthread_start(coordinator);
  for (int i = 0; i< N; i++){
    id[i]=i;
    amount[i]=0;
    contributed[i]=0;
    done_bidding[i] = 0;
    pthread_create(&buyer[i], NULL, &buyer_func, &id[i]);
  }
  for (int i = 0; i< N; i++)
    pthread_join(buyer[i], NULL);
  int total_amount = 0;
  for (int i = 0; i< N; i++){
    __VERIFIER_assume(done_bidding[i] == 1);
      total_amount += contributed[i]*amount[i];
  }
  int success = price > 0 ? 0 : 1;
  assert(success == 0 || total_amount < p);
}
