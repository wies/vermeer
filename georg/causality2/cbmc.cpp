/*
 * cbmc.cpp
 *
 *  Created on: Nov 26, 2014
 *      Author: andi
 */

#include "cbmc.h"

#include <signal.h>
#include <cstdlib>
#include <cstring>

#include <iostream>
#include <sstream>

// shared memory includes
#include <cstdio>
#include <sys/shm.h>
#include <sys/stat.h>

// semaphore includes
#include <fcntl.h>           /* For O_* constants */
#include <sys/stat.h>        /* For mode constants */
#include <semaphore.h>

// thread includes
#include <pthread.h>

cmdline_cbmct::cmdline_cbmct(const char* path_) : path(path_){

}

cmdline_cbmct::~cmdline_cbmct() {

}

bool cmdline_cbmct::run(const char* c_file, const char* output_file) {
	const int CBMC_SAT = 10;
	const int CBMC_UNSAT = 0;

	::std::stringstream cbmc_cmd;
	cbmc_cmd << path << " --function foo " << c_file << " > " << output_file;
	int ret = system(cbmc_cmd.str().c_str());

	if (WIFSIGNALED(ret) && (WTERMSIG(ret) == SIGINT || WTERMSIG(ret) == SIGQUIT)) {
		::std::cout << "ERROR" << ::std::endl;
		exit(EXIT_FAILURE);
	}

	if (WEXITSTATUS(ret) != CBMC_SAT) {
		if (WEXITSTATUS(ret) == CBMC_UNSAT) {
			return false;
		}
		else {
			::std::cout << "ERROR" << ::std::endl;
			exit(EXIT_FAILURE);
		}
	}

	return true;
}

incremental_cbmct::incremental_cbmct(const char* path_, unsigned semaphore_identifier_) : path(path_), semaphore_identifier(semaphore_identifier_) {
    cbmc_semaphore_name = "/cbmc_semaphore" + ::std::to_string(semaphore_identifier);
    local_semaphore_name = "/local_semaphore" + ::std::to_string(semaphore_identifier);
}

incremental_cbmct::~incremental_cbmct() {
    // TODO implement automatic stopping if this was not done by the application!

}

void* run_cbmc_thread(void* params_) {
	cbmc_parameterst* params = (cbmc_parameterst*)params_;

	const int CBMC_SAT = 10;
	const int CBMC_UNSAT = 0;

	::std::stringstream cbmc_cmd;
	cbmc_cmd << params->path << " --shm_segment_id " << params->segment_id << " --function foo " << params->c_file << " > " << params->output_file;
	::std::cout << "[" << cbmc_cmd.str() << "]" << ::std::endl;
	int ret = system(cbmc_cmd.str().c_str());

	if (WIFSIGNALED(ret) && (WTERMSIG(ret) == SIGINT || WTERMSIG(ret) == SIGQUIT)) {
		params->ret_value = ERROR;
	}

	if (WEXITSTATUS(ret) != CBMC_SAT) {
		if (WEXITSTATUS(ret) == CBMC_UNSAT) {
			params->ret_value = UNSAT;
		}
		else {
			params->ret_value = ERROR;
		}
	}
	else {
		params->ret_value = SAT;
	}

	pthread_exit(NULL);
}

void incremental_cbmct::start(const char* c_file, const char* output_file) {
    // TODO check whether CBMC was actually started! Implement state-machine.

	// we assume that variable thread is not used at the moment
	// TODO either generalize or implement a check


	// create shared memory
	shm_segment_id = shmget (IPC_PRIVATE, sizeof(cbmc_shmt), IPC_CREAT | IPC_EXCL | S_IRUSR | S_IWUSR);
	shared_memory = (cbmc_shmt*) shmat (shm_segment_id, NULL, 0);
	shared_memory->action = IDLE;
	shared_memory->result = false;
	shared_memory->semaphore_identifier = semaphore_identifier;


	// create semaphores
	cbmc_semaphore = sem_open(cbmc_semaphore_name.c_str(), O_CREAT | O_EXCL, S_IRWXU|S_IRWXG, 0);
	local_semaphore = sem_open(local_semaphore_name.c_str(), O_CREAT | O_EXCL, S_IRWXU|S_IRWXG, 0);


	// start thread
	::std::cout << "[SyMPC] starting a thread for CBMC ..." << ::std::endl;

	// TODO put params into a session?
	params.path = path.c_str();
	params.c_file = c_file;
	params.output_file = output_file;
	params.segment_id = shm_segment_id;

	pthread_create(&cbmc_thread, NULL, &run_cbmc_thread, (void*)&params);


	// wait for CBMC being initialized
	sem_wait(local_semaphore); // CBMC will increase this semaphore after it is initialized
}

bool incremental_cbmct::check() {
	// TODO create special communication method
	// set CBMC action
	shared_memory->action = RUN;
	shared_memory->result = false;

	// signal CBMC
	sem_post(cbmc_semaphore);

	// wait for CBMC to finish
	sem_wait(local_semaphore);


	// interpret result
	return shared_memory->result;
}

unsigned char incremental_cbmct::query_value(const ::std::string & var_name) {
    return query_value(var_name.c_str());
}

unsigned char incremental_cbmct::query_value(const char* var_name) {
	// TODO create special communication method
	// set CBMC action
	shared_memory->action = QUERY_VALUE;
	shared_memory->result = false;

	// TODO add check for length of var_name!
	strcpy(shared_memory->var_name, var_name);

	// signal CBMC
	sem_post(cbmc_semaphore);

	// wait for CBMC to finish
	sem_wait(local_semaphore);

	return shared_memory->var_value;
}

unsigned char incremental_cbmct::query_for_bits_in_unsat_core(const ::std::string & var_name) {
    return query_for_bits_in_unsat_core(var_name.c_str());
}

unsigned char incremental_cbmct::query_for_bits_in_unsat_core(const char* var_name) {
    // TODO create special communication method
	// set CBMC action
	shared_memory->action = QUERY_FOR_BITS_IN_UNSAT_CORE;
	shared_memory->result = false;
	shared_memory->var_value = 0;

	// TODO add check for length of var_name!
	strcpy(shared_memory->var_name, var_name);

	// signal CBMC
	sem_post(cbmc_semaphore);

	// wait for CBMC to finish
	sem_wait(local_semaphore);

	return shared_memory->var_value;
}

void incremental_cbmct::extend_blocking_clause(const ::std::string & var_name, unsigned char blocking_clause_pattern, unsigned char phase_pattern) {
    extend_blocking_clause(var_name.c_str(), blocking_clause_pattern, phase_pattern);
}

void incremental_cbmct::extend_blocking_clause(const char* var_name, unsigned char blocking_clause_pattern, unsigned char phase_pattern) {
    // TODO create special communication method
	// set CBMC action
	shared_memory->action = EXTEND_BLOCKING_CLAUSE;
	shared_memory->result = false;

	// TODO add check for length of var_name!
	strcpy(shared_memory->var_name, var_name);

	shared_memory->blocking_clause_pattern = blocking_clause_pattern;
	shared_memory->var_value = phase_pattern;

    // signal CBMC
	sem_post(cbmc_semaphore);

	// wait for CBMC to finish
	sem_wait(local_semaphore);
}

void incremental_cbmct::finish_blocking_clause() {
    // TODO create special communication method
	// set CBMC action
	shared_memory->action = FINISH_BLOCKING_CLAUSE;
	shared_memory->result = false;

    // signal CBMC
	sem_post(cbmc_semaphore);

	// wait for CBMC to finish
	sem_wait(local_semaphore);
}

void incremental_cbmct::clear_assumptions() {
    // TODO create special communication method
	// set CBMC action
	shared_memory->action = CLEAR_ASSUMPTIONS;
	shared_memory->result = false;

    // signal CBMC
	sem_post(cbmc_semaphore);

	// wait for CBMC to finish
	sem_wait(local_semaphore);
}

void incremental_cbmct::assume_value(const ::std::string & var_name, unsigned char value) {
    assume_value(var_name.c_str(), value);
}

void incremental_cbmct::assume_value(const char* var_name, unsigned char value) {
    // TODO create special communication method
	// set CBMC action
	shared_memory->action = ASSUME_VALUE;
	shared_memory->result = false;

	// TODO add check for length of var_name!
	strcpy(shared_memory->var_name, var_name);

	shared_memory->var_value = value;

	// signal CBMC
	sem_post(cbmc_semaphore);

	// wait for CBMC to finish
	sem_wait(local_semaphore);
}

void incremental_cbmct::list_variable_names() {
	// TODO create special communication method
	// set next action for CBMC to STOP
	shared_memory->action = LIST_VARIABLE_NAMES;
	shared_memory->result = false;

    // signal CBMC
	sem_post(cbmc_semaphore);

	// wait for CBMC to finish
	sem_wait(local_semaphore);
}

void incremental_cbmct::analyze_unsat_core() {
    // TODO create special communication method
	// set next action for CBMC to STOP
	shared_memory->action = ANALYZE_UNSAT_CORE;
	shared_memory->result = false;

    // signal CBMC
	sem_post(cbmc_semaphore);

	// wait for CBMC to finish
	sem_wait(local_semaphore);
}

void incremental_cbmct::stop() {
	// TODO create special communication method
	// set next action for CBMC to STOP
	shared_memory->action = STOP;
	shared_memory->result = false;

	// signal CBMC
	sem_post(cbmc_semaphore);

	// wait for CBMC to finish
	sem_wait(local_semaphore);




	// wait for CBMC thread to finish
	pthread_join(cbmc_thread, NULL);

	::std::cout << "[SyMPC] CBMC thread stopped ..." << ::std::endl;


	// deallocate semaphore
	sem_close(cbmc_semaphore);
	sem_unlink(cbmc_semaphore_name.c_str());

	sem_close(local_semaphore);
	sem_unlink(local_semaphore_name.c_str());


	// deallocate shared memory
	shmdt (shared_memory);
	shmctl (shm_segment_id, IPC_RMID, 0);
}

