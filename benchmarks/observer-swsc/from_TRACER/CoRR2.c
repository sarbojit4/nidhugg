/* Copyright (C) 2018
 * This benchmark is part of SWSC
 */

/* There are N^4+2N^3+2N^2+3N+1 weak traces */

#include <assert.h>
#include <stdint.h>
#include <stdatomic.h>
#include <pthread.h>

#ifndef N
#  warning "N was not defined"
#  define N 6
#endif

atomic_int vars[1];


void *writer(void *arg){
  	int tid = *((int *)arg);
  	atomic_store_explicit(&vars[0], tid, memory_order_seq_cst);
	return NULL;
}


void *reader(void *arg){
  	atomic_load_explicit(&vars[0], memory_order_seq_cst);
  	atomic_load_explicit(&vars[0], memory_order_seq_cst);
	return NULL;
}

int arg[N];
int main(int argc, char **argv){
  	pthread_t ws[N];
  	pthread_t rs[2];
  
  
  	atomic_init(&vars[0], 0);
  
  	for (int i=0; i<N; i++) {
    	arg[i]=i;
    	pthread_create(&ws[i], NULL, writer, &arg[i]);
  	}
  
  	pthread_create(&rs[0], NULL, reader, NULL);
  	pthread_create(&rs[1], NULL, reader, NULL);
  
  	for (int i=0; i<N; i++) {
    	pthread_join(ws[i], NULL);
  	}
  
  	pthread_join(rs[0], NULL);
  	pthread_join(rs[1], NULL);
  
	return 0;
}
