#include <stdio.h>
#include <stdatomic.h>
#include <pthread.h>
#include <assert.h>
#include "qthread.h"

#ifndef N
#define N 3
#endif

#define STORAGE_SIZE 4

typedef struct{
    atomic_int val;
    atomic_int deleted;
} slot;

slot storage[STORAGE_SIZE];

qthread_t server[N];
pthread_t client[N];

typedef struct{
    int key;// key or deleted status
    int num;
} req_t;
req_t reqst[N][N*16];
int Index[N];

void __VERIFIER_assume(intptr_t);

int hash_of(int i){ return i; }

void do_write(void *arg) {
  int index = hash_of((*(req_t *)arg).key);
  int num = (*(req_t *)arg).num;
  if(storage[index].deleted != 1){
    atomic_store_explicit(&(storage[index].val), num, memory_order_seq_cst);
    atomic_store_explicit(&(storage[index].deleted), 0, memory_order_seq_cst);
  }
  assert(storage[index].val == num || storage[index].deleted == 1);
}

void do_delete(void *arg) {
  int index = hash_of((*(req_t *)arg).key);
  atomic_store_explicit(&(storage[index].deleted), 1, memory_order_seq_cst);
}

void do_read(void *arg) {
  int index = hash_of((*(req_t *)arg).key);
  if(storage[index].deleted != 1){
    (*(req_t *)arg).key = atomic_load_explicit(&(storage[index].deleted), memory_order_seq_cst);
    (*(req_t *)arg).num = atomic_load_explicit(&(storage[index].val), memory_order_seq_cst);
  }
}

//------------------------------------------//

//-----------------socket-------------------//

void *socket_listener(){
    qthread_exec();
    return NULL;
}

void create_servers(){
    for(int i = 0; i < N; i++){
        qthread_create(&server[i], &socket_listener, NULL);
        qthread_start(server[i]);
    }
}

//------------------------------------------//

//---------------clients--------------------//
void *client_func(void *arg){
    int ind = *(int *)arg;
      reqst[ind][0].key = 0;
      reqst[ind][0].num = 3;
      qthread_post_event(server[ind], do_write, &reqst[ind][0]);
      reqst[ind][1].key = 2;
      reqst[ind][1].num = 3;
      qthread_post_event(server[ind], do_read, &reqst[ind][1]);
      reqst[ind][2].key = 3;
      reqst[ind][2].num = 3;
      qthread_post_event(server[ind], do_write, &reqst[ind][2]);
      reqst[ind][3].key = 2;
      reqst[ind][3].num = 3;
      //qthread_post_event(server[ind], do_read, &reqst[ind][3]);
      reqst[ind][4].key = 0;
      reqst[ind][4].num = 3;
      qthread_post_event(server[ind], do_delete, &reqst[ind][4]);
      return NULL;
}

void create_clients(){
  for(int i = 0; i < N; i++){
    Index[i] = i;
    pthread_create(&client[i], NULL, &client_func, &Index[i]);
  }
}

int main(){
  for(int i = 0; i < STORAGE_SIZE; i++)
    atomic_store_explicit(&(storage[i].deleted), 1, memory_order_seq_cst);
    create_servers();
    create_clients();
    return 0;
}
