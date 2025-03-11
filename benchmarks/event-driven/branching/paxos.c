#include <stdio.h>
#include <stdatomic.h>
#include <pthread.h>
#include <assert.h>
#include "qthread.h"

#ifndef M
#  warning "M was not defined; defining it as 1"
#  define M 1
#endif

#ifndef N
#  warning "N was not defined; defining it as 2"
#  define N 2
#endif

#ifndef MAX_ROUNDS
#  warning "MAX_ROUNDS was not defined; defining it as 1"
#  define MAX_ROUNDS 1
#endif


typedef struct {
  atomic_int prop;
  atomic_int value;
} value_t;

typedef struct {
  atomic_int proposer_id;
  atomic_int acceptor_id;
  atomic_int round;
  atomic_int prop_val;
  atomic_int val;  
} param_t;

////////////////////////////
pthread_t timer[M];
qthread_t acceptor[N];
qthread_t proposer[M];
atomic_int propose_val[M];
atomic_int last_promise[N]; //lastRecvProposal
atomic_int last_val[N]; //lastRecvProposal
atomic_int last_accepted_val[N]; //
atomic_int completed_rounds[M];
atomic_int timeout[M];
atomic_int no_of_promises[M];
////////////////////////////

void __VERIFIER_assume(int truth){}
void prepare(void *par);
void propose(void *par);
void accept(void *par);
void accepted(void *par);
void proposer_phase_two(void *par);

void *timer_func(void *par){
  int prop_id = (*(int *)par);
  free(par);
  timeout[prop_id] = 1;
  return NULL;
}

///////////////////////////////////Proposer////////////////////////////////////////

void prepare(void *par) {
  int prop_id = (*(int *)par);
  free(par);
  no_of_promises[prop_id] = 0;
  propose_val[prop_id]++;
  for(int i = 0; i < N; i++){
    last_val[i] = 0;
    param_t *msg_par = (param_t*)malloc(sizeof(param_t));
    if(!msg_par) return;
    msg_par->proposer_id = prop_id;
    msg_par->acceptor_id = i;
    msg_par->round = completed_rounds[prop_id];
    msg_par->prop_val = propose_val[prop_id];
    qthread_post_event(acceptor[i], &propose, msg_par);
  }
}

void accept(void *par) {
  atomic_int prop_id = (*(param_t *)par).proposer_id;
  atomic_int acc_id = (*(param_t *)par).acceptor_id;
  atomic_int round = (*(param_t *)par).round;
  atomic_int prop_val = (*(param_t *)par).prop_val;
  atomic_int val = (*(param_t *)par).val;
  free(par);
  //if(++no_of_promises[prop_id] >= N/2+1) return;
  /* else if(timeout[prop_id] == 1){ */
  /*   if(completed_rounds[prop_id] >= MAX_ROUNDS) return; */
  /*   last_accepted_val[acc_id] = val; */
  /*   int *msg_par = malloc(sizeof(int)); */
  /*   *msg_par = prop_id; */
  /*   completed_rounds[prop_id]++; */
  /*   qthread_post_event(proposer[prop_id], &prepare, msg_par);     */
  /* } */
  if(//timeout[prop_id] == 0 && 
     ++no_of_promises[prop_id] == N/2+1){
    last_accepted_val[acc_id] = val;
    atomic_int max_val = 0;
    for(int i = 0; i < N; i++){
      if(max_val < last_val[i]) max_val = last_val[i];
    }
    for(int i = 0; i < N; i++){
      param_t *msg_par = (param_t*)malloc(sizeof(param_t));
      if(!msg_par) return;
      msg_par->proposer_id = prop_id;
      msg_par->acceptor_id = acc_id;
      msg_par->round = round;
      msg_par->prop_val = prop_val;
      msg_par->val = max_val;
      qthread_post_event(acceptor[i], &accepted, msg_par);    
    }
    completed_rounds[prop_id]++;
  }
}

///////////////////////////////////Acceptor//////////////////////////////////////////////

void propose(void *par){
  atomic_int prop_id = (*(param_t *)par).proposer_id;
  atomic_int acc_id = (*(param_t *)par).acceptor_id;
  atomic_int round = (*(param_t *)par).round;
  atomic_int prop_val = (*(param_t *)par).prop_val;
  free(par);
  if(last_promise[acc_id] < prop_val){
    param_t *msg_par = (param_t*)malloc(sizeof(param_t));
    if(!msg_par) return;
    msg_par->proposer_id = prop_id;
    msg_par->acceptor_id = acc_id;
    msg_par->round = round;
    msg_par->prop_val = last_promise[acc_id];
    msg_par->val = last_val[acc_id];
    last_promise[acc_id] = prop_val;
    qthread_post_event(proposer[prop_id], &accept, msg_par);
  }
    
}

void accepted(void *par) {
  atomic_int prop_id = ((param_t *)par)->proposer_id;
  atomic_int round = ((param_t *)par)->round;
  atomic_int prop_val = (*(param_t *)par).prop_val;
  assert(0 <= prop_id && prop_id < M);
  //accepted[prop_id]++;
  /* if(round > last_promised[prop_id].round || */
  /*    (round == last_promised[prop_id].round &&  */
  /*     prop_id > last_promised[prop_id].proposer_id)){ */
  /*   last_promised[prop_id].round = round; */
  /*   last_promised[prop_id].prop_val = prop_val; */
  /*   if(last_promised[prop_id].round==0) last_promised[prop_id].proposer_id = 0; */
  /*   else last_promised[prop_id].proposer_id = prop_id; */
  /* } */
  /* if(accepted[prop_id] == (N/2)+1){ */
  /*   qthread_post_event(proposer[prop_id], &proposer_phase_two, par); */
  /* } */
}
//////////////////////////////////Main////////////////////////////////////////////

void *handler_func(void *i){ 
  int quit = qthread_exec();
  return 0;
}

int main(){
  for(int i = 0; i < N; i++){
    last_promise[i] = 0; //lastRecvProposal
    last_val[i] = 0; //lastRecvProposal
    qthread_create(&acceptor[i], &handler_func, NULL);
    qthread_start(acceptor[i]);
  }

  for(int i = 0; i < M; i++){
    propose_val[i] = 0;
    completed_rounds[i] = 0;
    timeout[i] = 0;
    no_of_promises[i] = 0;
    
    qthread_create(&proposer[i], &handler_func, NULL);
    qthread_start(proposer[i]);
    
    int *id1 = malloc(sizeof(atomic_int));
    if(!id1) return 1;
    *id1 = i;
    pthread_create(&timer[i], NULL, &timer_func, id1);
    
    int *id2 = malloc(sizeof(atomic_int));
    if(!id2) return -1;
    *id2 = i;
    qthread_post_event(proposer[i], &prepare, id2);
  }
  for(int i = 0; i < M; i++){
    // pthread_join(timer[i], NULL);
  }
}
