#include<stdio.h>
#include<stdlib.h>
#include<pthread.h>
#include<assert.h>
#include"qthread.h"

#ifndef N
#  warning "N was not defined; defining it as 2"
#  define N 2
#endif

struct device{
  int owner;
};

typedef struct{
  qthread_t handler;
  int gid;
  int fd;
  int to_write;
} arg_t;

struct device dev;
int state = 0;
int last_gid = 1;
int num = 0;
int num_msg = 0;

int new_gid(){ return last_gid++; }

int random_int(){
  state = state + 17;
  return (state*13)%7;
}

int get_write() {
  return 8;
}

int get_fd() {
  return random_int();
}

int transfer(int fd, struct device dev){
  return 2;
}

void write(void *arg) {
  qthread_t handler = ((arg_t *)arg)->handler;
  int gid = ((arg_t *)arg)->gid;
  int fd = ((arg_t *)arg)->fd;
  int to_write = ((arg_t *)arg)->to_write;
  //assert(dev.owner == gid);
  to_write -= transfer(fd, dev);
  if(to_write > 0){
    ((arg_t *)arg)->to_write = to_write;
    qthread_post_event(handler, &write, arg);
    return;
  }
  dev.owner = 0;
  free(arg);
}

void *handler_func(void *arg){
  qthread_exec();
  return NULL;
}

void new_client(void *handler){
  if(dev.owner>0 && num_msg <= N){
    num_msg++;
    qthread_post_event(*(qthread_t *)handler, &new_client, handler);
  }
  else{
    arg_t *arg = malloc(sizeof(arg_t));
    arg->handler = *(qthread_t *)handler;
    arg->gid = new_gid();
    arg->fd = get_fd();
    arg->to_write = get_write();
    dev.owner = arg->gid;
    qthread_post_event(arg->handler, &write, arg);
    free(handler);
  }
}
void listen(void *socket){
  qthread_t *handler = malloc(sizeof(qthread_t));
  qthread_create(handler, &handler_func, NULL);
  qthread_start(*handler);
  qthread_post_event(*handler, &new_client, handler);
  num++;
  if(num >= N) free(socket);
  else qthread_post_event(*(qthread_t *)socket, &listen, socket);
}

int main(){
  dev.owner = 0;
  qthread_t *socket = malloc(sizeof(qthread_t));
  qthread_create(socket, &handler_func, NULL);
  qthread_start(*socket);
  qthread_post_event(*socket, &listen, socket);
  return 0;
}
