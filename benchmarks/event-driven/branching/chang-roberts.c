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
atomic_int a[N];
param p[N];
param p2[N][N];

void announce(void *par) {
  atomic_int p_own = (*(param *)par).own;
  atomic_int p_new = (*(param *)par).new;

  // write the index of the leader node
  atomic_store_explicit(&decision[p_own], p_new, memory_order_seq_cst);
}

void msg(void *par) {
  atomic_int p_own = (*(param *)par).own;
  atomic_int p_new = (*(param *)par).new;
  
  if (p_own == p_new) {
    // if a node receives its own id then it will announce to all nodes it is the leader
    for (int i = 0; i < N; i++) {
      p2[p_own][i].own = i;
      p2[p_own][i].new = p_own;
      qthread_post_event(nodes[i], &announce, &p2[p_own][i]);
    }
  } else {
    atomic_int own_val = atomic_load_explicit(&ids[p_own], memory_order_seq_cst);
    atomic_int new_val = atomic_load_explicit(&ids[p_new], memory_order_seq_cst);
    if (new_val > own_val) {
      // if a node receives an id greater than its own, replace its own id and forward the new id
      atomic_store_explicit(&ids[p_own], new_val, memory_order_seq_cst);
      p2[p_own][(p_own+1)%N].own = (p_own + 1) % N;
      p2[p_own][(p_own+1)%N].new = p_new;
      qthread_post_event(nodes[(p_own + 1) % N], &msg, &p2[p_own][(p_own+1)%N]);
    }
  }
}

// initial message to make all nodes start sending messages
void init_msg(void *par) {
  int i = *(int *)par;
  p[i].own = (i + 1) % N;
  p[i].new = i;
  qthread_post_event(nodes[(i+1) % N], &msg, &p[i]);
}

// initializes all nodes by making them send a messages to their neighbor
void *init(void *par) {
  for (int i = 0; i < N; i++) {
    a[i] = i;
    qthread_post_event(nodes[i], &init_msg, &a[i]);
  }
  return 0;
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
  
  pthread_create(&t, NULL, &init, NULL);
  
  pthread_join(t, NULL);
  return 0;
}
