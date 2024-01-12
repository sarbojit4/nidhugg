#include <stdio.h>
#include <stdlib.h>
#include <pthread.h>
#include <stdatomic.h>

#ifndef N
# define N 7
#endif

atomic_int x;
atomic_int y;

atomic_int done[N];

void __VERIFIER_assume(int );

void *thread_n(void *arg)
{
	intptr_t id = (intptr_t) arg;

	int r = x;
	x = r + 1;
	done[id] = 1;
	return NULL;
}

void *thread_1(void *unused)
{
	int r = x;
	x = r + 1;
	return NULL;
}

void *thread_2(void *unused)
{
	for (int i = 0u; i < N; i++)
		__VERIFIER_assume(done[i] == 1);

	int r = x;
	x = r + 1;
	return NULL;
}

int main()
{
	pthread_t t1, t2;

	if (pthread_create(&t1, NULL, thread_1, NULL))
		abort();

	pthread_t t[N];

	for (int i = 0u; i < N; i++)
		pthread_create(&t[i], NULL, thread_n, (void *) i);
	for (int i = 0u; i < N; i++)
		pthread_join(t[i], NULL);

	if (pthread_create(&t2, NULL, thread_2, NULL))
		abort();

	return 0;
}
