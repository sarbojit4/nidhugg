#include <stdio.h>
#include <stdlib.h>
#include <pthread.h>
#include <stdatomic.h>

#ifndef N
# define N 2
#endif

atomic_int x;
atomic_int y;

void *thread_n(void *unused)
{
	atomic_store_explicit(&y, 1, memory_order_seq_cst);
	return NULL;
}

void *thread_1(void *unused)
{
	atomic_store_explicit(&x, 1, memory_order_seq_cst);
	return NULL;
}

void *thread_2(void *unused)
{
	pthread_t t[N];

	for (int i = 0u; i < N; i++)
		pthread_create(&t[i], NULL, thread_n, NULL);
	for (int i = 0u; i < N; i++)
		pthread_join(t[i], NULL);

	atomic_int a=atomic_load_explicit(&x, memory_order_seq_cst);
	return NULL;
}

int main()
{
	pthread_t t1, t2;

	if (pthread_create(&t1, NULL, thread_1, NULL))
		abort();
	if (pthread_create(&t2, NULL, thread_2, NULL))
		abort();

	return 0;
}
