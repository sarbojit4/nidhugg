#include <stdint.h>
#include <stdatomic.h>
#include <pthread.h>
// ((N+1)^N)*(N!) traces
#ifndef N
#  warning "N was not defined, assuming N=3"
#  define N 3
#endif

atomic_int var;

void *writer(void *arg) {
  atomic_store(&var, 0);
  return NULL;
}
void *reader(void *arg) {
  atomic_int a = atomic_load(&var);
  return NULL;
}
void *foo(void *arg) {
  return NULL;
}

int main(int argc, char *argv[]) {
  pthread_t t[3*N];

  for (int i = 0; i < N; i++) {
    pthread_create(&t[i], NULL, foo, (void*)(intptr_t)(i+1));
  }
  for (int i = N; i < 2*N; i++) {
    pthread_create(&t[i], NULL, writer, (void*)(intptr_t)(i+1));
  }
  for (int i = 2*N; i < 3*N; i++) {
    pthread_create(&t[i], NULL, reader, (void*)(intptr_t)(i+1));
  }

  for (int i = 0; i < 3*N; i++) {
    pthread_join(t[i], NULL);
  }

  return 0;
}
