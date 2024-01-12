/* Adapted from: https://gitlab.com/sosy-lab/benchmarking/sv-benchmarks/-/blob/main/c/pthread/fib_safe.h */

#include <assert.h>
#include <stdatomic.h>
#include <pthread.h>

atomic_int i, j;

#ifndef N
#  warning "N not defined, assuming 3"
#  define N 3
#endif

#define TIMES 2*N+2

int p, q;

void *t1(void* arg){
  for (p = 0; p < N; p++) {
    atomic_store(&i, atomic_load(&i) + atomic_load(&j));
  }

  return NULL;
}

void *t2(void* arg){
  for (q = 0; q < N; q++)
    atomic_store(&j, atomic_load(&j) + atomic_load(&i));

  return NULL;
}

int cur = 1, prev = 0, next = 0;
int x;

int fib(int n) {
  //int cur = 1, prev = 0;
    for (x = 0; x < TIMES; x++) {
	next = prev+cur;
	prev = cur;
	cur = next;
    }
    return prev;
}

int main(int argc, char **argv) {
  pthread_t id1, id2;

  atomic_init(&i, 1);
  atomic_init(&j, 1);

  pthread_create(&id1, NULL, t1, NULL);
  pthread_create(&id2, NULL, t2, NULL);

  int correct = fib(2+2*N);
  assert(atomic_load(&i) <= correct && atomic_load(&j) <= correct);

  return 0;
}
