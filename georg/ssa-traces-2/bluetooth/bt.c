#include <stdio.h>
#include <pthread.h>
#include "crest.h"
#include "../../assert.h"

int pendingIO;
int stoppingEvent;
int stopped , stoppingFlag;
int status1,status2;

void func1(int *input){
	
	int in;
	  CREST_var_int(in, CREST_LOCAL_VAR, "in");
	in = *input;
	
	if(in == 1){
		CREST_scope_begin();
		printf("in ADD!\n");
	    if(stoppingFlag==1){
	    	CREST_scope_begin();
	        status1 = -1;
	        CREST_scope_end();
		}
	    else{
	    	CREST_scope_begin();
		    pendingIO++;
		    status1 = 0;
		    CREST_scope_end();
	    }
	    if (status1==0) {
	    	CREST_scope_begin();
               assert(stopped != 1);
	       /*if (stopped==1){
	           printf("Errrorr\n");
		       //assert(0);
	       }*/
	        printf("do actual work\n");
	        CREST_scope_end();
		}
	    pendingIO--;
		if(pendingIO==0) {
			CREST_scope_begin();
		    stoppingEvent = 1;
		    CREST_scope_end();
		}
		CREST_scope_end();
	}
	else{
		CREST_scope_begin();
		printf("in STOP!\n");
		stoppingFlag = 1;
		pendingIO--;
		if (pendingIO == 0) {
			CREST_scope_begin();
			stoppingEvent=1;
			CREST_scope_end();
		}
		stopped = 1;
		CREST_scope_end();
	}
	
	pthread_exit(NULL);
}

void func2(int *input){
	
	int in;
	  CREST_var_int(in, CREST_LOCAL_VAR, "in");
	in = *input;
	
	if(in == 1){
		CREST_scope_begin();
		printf("in ADD!\n");
	    if(stoppingFlag==1){
	    	CREST_scope_begin();
	        status2 = -1;
	        CREST_scope_end();
		}
	    else{
	    	CREST_scope_begin();
		    pendingIO++;
		    status2 = 0;
		    CREST_scope_end();
	    }
	    if (status2==0) {
	    	CREST_scope_begin();
	       if (stopped==1){
	    	   CREST_scope_begin();
	           printf("Errrorr\n");
	           CREST_scope_end();
		       //assert(0);
	       }
	        printf("do actual work\n");
	        CREST_scope_end();
		}
	    pendingIO--;
		if(pendingIO==0) {
			CREST_scope_begin();
		    stoppingEvent = 1;
		    CREST_scope_end();
		}
		CREST_scope_end();
	}
	else{
		CREST_scope_begin();
		printf("in STOP!\n");
		stoppingFlag = 1;
		pendingIO--;
		if (pendingIO == 0) {
			CREST_scope_begin();
			stoppingEvent=1;
			CREST_scope_end();
		}
		stopped = 1;
		CREST_scope_end();
	}
	
	pthread_exit(NULL);
}

int main(){

	stoppingEvent = 0;
	stopped = 0;
	stoppingFlag = 0;
	pendingIO = 1; 

       int input1, input2;

	printf("in main\n");
	CREST_int(input1);
	CREST_var_int(input1, CREST_LOCAL_VAR, "input1");

	CREST_int(input2);
	CREST_var_int(input2, CREST_LOCAL_VAR, "input2");

    CREST_shared_int(stoppingEvent);
	CREST_shared_int(stopped);
	CREST_shared_int(stoppingFlag);
	CREST_shared_int(pendingIO);
	
	  CREST_var_int(stoppingEvent, CREST_SHARED_VAR, "stoppingEvent");
	  CREST_var_int(stopped, CREST_SHARED_VAR, "stopped");
	  CREST_var_int(stoppingFlag, CREST_SHARED_VAR, "stoppingFlag");
	  CREST_var_int(pendingIO, CREST_SHARED_VAR, "pendingIO");

	  CREST_var_int(status1, CREST_SHARED_VAR, "status1");
	  CREST_var_int(status2, CREST_SHARED_VAR, "status2");


	pthread_t pt1;
	pthread_t pt2;

	pthread_create( &pt1, NULL, &func1, &input1 );
  	pthread_create( &pt2, NULL, &func2, &input2 );
	
	//pthread_join(pt1, NULL); 
	//pthread_join(pt2, NULL); 

	pthread_exit(NULL);

	return 0;
}
