#include<stdio.h>
#include<stdatomic.h>
#include<pthread.h>
#include"qthread.h"

#ifndef N
#define N 3
#endif

#define STORAGE_SIZE 32

typedef struct{
    atomic_int val;
    atomic_int deleted;
} slot;

slot storage[STORAGE_SIZE];

qthread_t server[N];
qthread_t client[N];

typedef struct{
    qthread_t client;
    int key;// key or deleted status
    int num;
} req_t;
req_t reqst[N][N*16];
int Index[N];

void recv_read_result(void *arg);
void recv_write_result(void *arg);

int hash_of(int i){ return i; }

void do_write(void *arg) {
  int index = hash_of((*(req_t *)arg).key);
  int num = (*(req_t *)arg).num;
  atomic_store_explicit(&(storage[index].val), num, memory_order_seq_cst);
  atomic_store_explicit(&(storage[index].deleted), 0, memory_order_seq_cst);
  //qthread_post_event((*(req_t *)arg).client, recv_write_result, arg);
}

void do_delete(void *arg) {
  int index = hash_of((*(req_t *)arg).key);
  atomic_store_explicit(&(storage[index].deleted), 1, memory_order_seq_cst);
  //qthread_post_event((*(req_t *)arg).client, recv_write_result, arg);
}

void do_read(void *arg) {
  int index = hash_of((*(req_t *)arg).key);
  (*(req_t *)arg).key = atomic_load_explicit(&(storage[index].deleted), memory_order_seq_cst);
  (*(req_t *)arg).num = atomic_load_explicit(&(storage[index].val), memory_order_seq_cst);
  //qthread_post_event((*(req_t *)arg).client, recv_read_result, arg); 
}

//------------------------------------------//

//-----------------socket-------------------//

void *socket_listener(){
    qthread_exec();
    return NULL;
}

void create_server_sockets(){
    for(int i = 0; i < N; i++){
        qthread_create(&server[i], &socket_listener, NULL);
        qthread_start(server[i]);
    }
}

//------------------------------------------//

//---------------clients--------------------//
void *client_func(void *arg){
  //Requests
  qthread_exec();
  return NULL;
}

void recv_read_result(void *arg){
    //qthread_post_event((*(req_t *)arg).client, recv_read_result, arg);
}

void recv_write_result(void *arg){
    //qthread_post_event((*(req_t *)arg).client, recv_write_result, arg);
}

void client_init_msg(void *arg){
    int ind = *(int *)arg;
      reqst[ind][0].client = client[ind];
      reqst[ind][0].key = 0;
      reqst[ind][0].num = 3;
      qthread_post_event(server[ind], do_write, &reqst[ind][0]);
      reqst[ind][1].client = client[ind];
      reqst[ind][1].key = 2;
      reqst[ind][1].num = 3;
      qthread_post_event(server[ind], do_read, &reqst[ind][1]);
      reqst[ind][2].client = client[ind];
      reqst[ind][2].key = 3;
      reqst[ind][2].num = 3;
      //qthread_post_event(server[ind], do_write, &reqst[ind][2]);
      reqst[ind][3].client = client[ind];
      reqst[ind][3].key = 2;
      reqst[ind][3].num = 3;
      qthread_post_event(server[ind], do_read, &reqst[ind][3]);
      reqst[ind][4].client = client[ind];
      reqst[ind][4].key = 0;
      reqst[ind][4].num = 3;
      qthread_post_event(server[ind], do_delete, &reqst[ind][4]);
  
}

void create_client_sockets(){
    for(int i = 0; i < N; i++)
        qthread_create(&client[i], &client_func, NULL);
}

void setup_client_requests(){
    for(int i = 0; i < N; i++){
        Index[i] = i;
        //printf("%d--\n", Index[i]);/////
	    qthread_post_event(client[i], client_init_msg, &Index[i]);
	}
}

void start_client_sockets(){
    for(int i = 0; i < N; i++)
        qthread_start(client[i]);
}

int main(){
    create_server_sockets();
    create_client_sockets();
    setup_client_requests();
    start_client_sockets();
    return 0;
}
