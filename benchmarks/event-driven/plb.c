#include <stdlib.h>
#include <pthread.h>
#include "qthread.h"

#ifndef N
#  warning "N was not defined; defining it as 5"
#  define N 5
#endif

typedef struct req_list{
  int id;
  struct req_list *next;
} req_list;

typedef struct{
  int id;
} client_t;

typedef struct{
  client_t *rc;
  int id;
} arg_t;

req_list* r;
qthread_t handler;

void client(void *arg){
  client_t *c = ((arg_t *)arg)->rc;
  int id = ((arg_t *)arg)->id;
  //---
  c->id = id;
  //---
  free(c);
  free((arg_t *)arg);
  return;
}

void reqs(void *arg){
  /*if(r == NULL){
    qthread_post_event(handler, &reqs, NULL);
    return;
  }*/
  arg_t *a = malloc(sizeof(arg_t));
  if(a == NULL) return;
  a->rc = malloc(sizeof(client_t));
  a->id = r->id;
  if(a->rc == NULL) return;
  qthread_post_event(handler, &client, a);
  r = r->next;
  if(r != NULL) qthread_post_event(handler, &reqs, NULL);
}

void *handler_func(void *i){
  qthread_exec();
  return 0;
}

int main(){
  req_list *prev,*curr;
  r = malloc(sizeof(req_list));
  r->id = 0;
  r->next = NULL;
  prev = r;
  int i;
  for(i=1; i<N; i++){
    curr = malloc(sizeof(req_list));
    if(curr == NULL) return 1;
    curr->id = i;
    curr->next = NULL;
    prev->next = curr;
    prev = curr;
  }
  qthread_create(&handler, &handler_func, NULL);
  qthread_start(handler);
  qthread_post_event(handler, &reqs, NULL);
  return 0;
}
