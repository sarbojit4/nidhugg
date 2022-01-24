#include <stdio.h>
#include <stdatomic.h>
#include <pthread.h>
#include "qthread.h"

#ifndef N
#  warning "N was not defined; defining it as 3"
#  define N 3
#endif

typedef struct {
  int own;
  int new;
} param;

qthread_t nodes[N];

atomic_int ids[N];
atomic_int decision[N];

void *announce(void *par) {
  param p = *(param *)par;
  
  // write the index of the leader node
  atomic_store_explicit(&decision[p.own], p.new, memory_order_seq_cst);
}

void *msg(void *par) {
  param p = *(param *)par;
  
  if (p.own = p.new) {
    // if a node receives its own id then it will announce to all nodes it is the leader
    for (int i = 0; i < N; i++) {
      param p2;
      p2.own = i;
      p2.new = p.own;
      qthread_post_event(nodes[i], &announce, &p2);
    }
  } else {
    atomic_int own_val = atomic_load_explicit(&ids[p.own], memory_order_seq_cst);
    atomic_int new_val = atomic_load_explicit(&ids[p.new], memory_order_seq_cst);
    if (new_val > own_val) {
      // if a node receives an id greater than its own, replace its own id and forward the new id
      atomic_store_explicit(&ids[p.own], new_val, memory_order_seq_cst);
      param p2;
      p2.own = (p.own + 1) % N;
      p2.new = p.new;
      qthread_post_event(nodes[(p.own + 1) % N], &msg, &p2);
    }  
  }
}

// initial message to make all nodes start sending messages
void *init_msg(void *par) {
  int i = *(int *)par;
  param p;
  p.own = (i + 1) % N;
  p.new = i;
  qthread_post_event(nodes[(i+1) % N], &msg, &p);
}

// initializes all nodes by making them send a messages to their neighbor
void *init(void *par) {
  for (int i = 0; i < N; i++) {
    qthread_post_event(nodes[i], &init_msg, &i);
  }
}

void *handler_func(void *i){ 
  int quit = qthread_exec();
  return 0;
}

int main() {
  for (int i = 0; i < N; i++) {
    ids[i] = N-i;
    decision[i] = -1;
    qthread_create(&nodes[i], &handler_func, NULL);
    qthread_start(nodes[i]);
  }
  
  pthread_t t;
  
  int a = 0;
  
  pthread_create(&t, NULL, &init, &a);
  
  pthread_join(t, NULL);
  
  for (int i = 0; i < N; i++) {
    qthread_wait(nodes[i], NULL);
  }
}
