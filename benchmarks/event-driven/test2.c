#include<stdio.h>
#include<stdatomic.h>
#include<pthread.h>
//using namespace std;
int qthread_create(int *tid, void *(*func)(void *), void *);
void qthread_wait(int tid, void *ret_val);
void qthread_start(int tid);
void qthread_post_event(int tid, void *(*func)(void *), void *); 
int qthread_exec();
atomic_int g;
void *message1(void *j){
 g=1;
 return 0;
}
void *message2(void *j){
  return 0;
}
void *thread1(void *i){
  qthread_post_event(1, &message1, i); 
  return 0;
}
void *thread2(void *i){
  qthread_post_event(1, &message2, i); 
  //qthread_post_event(1, &message2, i); 
  return 0;
}
void *handler_func(void *i){ 
  int quit=qthread_exec();
  return i; 
}
int main() {
  int tid1,tid2,tid3,tid4,handler;
  int a=2;
  qthread_create(&handler, &handler_func, &a);
  pthread_create(&tid1, NULL, &thread1, &tid1);
  pthread_create(&tid2, NULL, &thread2, &tid2);
  pthread_create(&tid3, NULL, &thread2, &tid2);
//  pthread_create(&tid4, NULL, &thread2, &tid2);
  pthread_join(tid1, NULL);
  pthread_join(tid2, NULL);
  pthread_join(tid3, NULL);
  //pthread_join(tid4, NULL);
  qthread_start(handler);
  qthread_wait(handler, NULL);
}
