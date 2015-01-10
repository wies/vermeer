#include <pthread.h>
#include <stdio.h>
#include <stdlib.h>
#include "crest.h"
#include "../../assert.h"

#define MAX_NUM_THREADS 10
#define NUM_THREADS 4

pthread_mutex_t mutex;
int x;
int inputs[MAX_NUM_THREADS];
pthread_t threads[MAX_NUM_THREADS];

void *thread_routine(void* arg)
{
	int* p;
	CREST_var_int(p, CREST_LOCAL_VAR, "p");
	p = (int*)arg;
    
	int in;
	CREST_var_int(in, CREST_LOCAL_VAR, "in");
	in = *p;

	int i;
	CREST_var_int(i, CREST_LOCAL_VAR, "i");

	if (in == 1) {
		CREST_scope_begin();

		for (i=0 ; i<9 ; i++) {
			CREST_scope_begin();

			int tmp;
			CREST_var_int(tmp, CREST_LOCAL_VAR, "tmp");

			pthread_mutex_lock(&mutex);

			tmp = x;
			tmp++;
			x = tmp;

			pthread_mutex_unlock(&mutex);

			assert(tmp != 24);
			CREST_scope_end();
		}

		CREST_scope_end();
	}
	else if (in == 2) {
		CREST_scope_begin();
		for (i=0 ; i<9 ; i++) {
			CREST_scope_begin();
			int tmp;
			CREST_var_int(tmp, CREST_LOCAL_VAR, "tmp");
			pthread_mutex_lock(&mutex);
			tmp = x;
			tmp += 10;
			x = tmp;
	      	pthread_mutex_unlock(&mutex);
			assert(tmp != 4390);
			CREST_scope_end();
		}
		CREST_scope_end();
	}
	else if (in == 3){
		CREST_scope_begin();
		for (i=0 ; i<9 ; i++){
			CREST_scope_begin();
			int tmp;
	        CREST_var_int(tmp, CREST_LOCAL_VAR, "tmp");
	      		pthread_mutex_lock(&mutex);
			tmp = x;
			tmp += 100;
			x = tmp;
	      		pthread_mutex_unlock(&mutex);		
			assert(tmp != 1256);
			CREST_scope_end();
		}
		CREST_scope_end();
	}
	else if (in == 4) {
		CREST_scope_begin();
		for (i=0 ; i<9 ; i++){
			CREST_scope_begin();
			int tmp;
	        CREST_var_int(tmp, CREST_LOCAL_VAR, "tmp");
	      		pthread_mutex_lock(&mutex);
			tmp = x;
			tmp += 1000;
			x = tmp;
	      		pthread_mutex_unlock(&mutex);		
			assert(tmp != 3849);
			CREST_scope_end();
		}
		CREST_scope_end();
	}

	pthread_exit(NULL);
}



int main(int argc, char* argv[]) 
{

  int i;
  CREST_var_int(i, CREST_LOCAL_VAR, "i");
  pthread_mutex_init(&(mutex), NULL);
  for(i=0; i< NUM_THREADS ; i++) {
	  CREST_scope_begin();
	  int* p;
	  __CrestInt(p);
	  CREST_var_int(p, CREST_LOCAL_VAR, "p");
	  p = inputs + i;
    	//CREST_int(inputs[i]);
	  CREST_scope_end();
  }

  CREST_shared_int(x);
  CREST_var_int(x, CREST_SHARED_VAR, "x");

  int t;
  CREST_var_int(t, CREST_LOCAL_VAR, "t");
  t = 0;
  while (t < NUM_THREADS) {
	  CREST_scope_begin();
	  int* p;
	  CREST_var_int(p, CREST_LOCAL_VAR, "p");
	  p = inputs + t;
	  pthread_create(&threads[t], NULL, thread_routine, (void *)p);
    
	  t = t + 1;
	  CREST_scope_end();
  }


  pthread_exit(NULL);
}

