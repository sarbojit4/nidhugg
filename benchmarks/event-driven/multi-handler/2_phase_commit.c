#include <stdio.h>
#include <stdatomic.h>
#include <pthread.h>
#include <stdlib.h>
#include "qthread.h"

//N! traces N! assume blocked traces
#ifndef N
#  warning "N was not defined; defining it as 5"
#  define N 5
#endif

qthread_t manager;
qthread_t node[N];
atomic_int ind = 0;
atomic_int id[N];
atomic_int vote[N];
atomic_int no_commit = 0;
atomic_int done[N];

void __VERIFIER_assume(int truth);

int rand_int(int id){
  int state = (id * 17)/7;
  return state%2;
}

void done_voting(void *_id){
  atomic_int id = *((atomic_int *)_id);
  no_commit += vote[id];
  done[ind] = 1;
  ind++;
}

void ask_vote(void *_id){
  atomic_int id = *((atomic_int *)_id);
  atomic_store_explicit(&vote[id], rand_int(id), memory_order_seq_cst);
  qthread_post_event(manager, &done_voting, _id);
}

void update(void *i){ 
  for(int i = 0; i < N; i++){
    qthread_post_event(node[i], &ask_vote, &id[i]);
  }
}

void *client_func(void *i){ 
  qthread_post_event(manager, &update, NULL);
  __VERIFIER_assume(done[N-1] == 1);
  atomic_int decision = 1 - no_commit;
  return NULL;
}

void *handler_func(void *i){ 
  qthread_exec();
  return 0;
}

int main(){
  qthread_create(&manager, &handler_func, NULL);
  qthread_start(manager);
  for (int i = 0; i < N; i++){
    id[i] = i;
    vote[i] = -1;
    done[i] = 0;
    qthread_create(&node[i], &handler_func, &id[i]);
    qthread_start(node[i]);
  }
  pthread_t client;
  pthread_create(&client, NULL, &client_func, NULL);
  pthread_join(client, NULL);
}
