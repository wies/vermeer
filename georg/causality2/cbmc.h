/*
 * cbmc.h
 *
 *  Created on: Nov 26, 2014
 *      Author: andi
 */

#ifndef CBMC_H_
#define CBMC_H_

#include <string>

#include <pthread.h>
#include <semaphore.h>

bool run_cbmc(const char* c_file, const char* output_file);

class cmdline_cbmct {
public:
	cmdline_cbmct(const char* path);
	virtual ~cmdline_cbmct();

	virtual bool run(const char* c_file, const char* output_file);

private:
	const ::std::string path;
};


enum return_valuet {
	SAT,
	UNSAT,
	ERROR
};

struct cbmc_parameterst {
	/* output */
	return_valuet ret_value;

	/* input */
	const char* c_file;
	const char* output_file;
	const char* path;

	/* process communication */
	int segment_id; // shared memory
};

enum cbmc_actiont {
	IDLE = 0,
	RUN = 1,
	STOP = 2,
	QUERY_VALUE = 3,
	ASSUME_VALUE = 4,
	CLEAR_ASSUMPTIONS = 5,
	LIST_VARIABLE_NAMES = 6,
	ANALYZE_UNSAT_CORE = 7,
	QUERY_FOR_BITS_IN_UNSAT_CORE = 8,
    EXTEND_BLOCKING_CLAUSE = 9,
    FINISH_BLOCKING_CLAUSE = 10
};

struct cbmc_shmt {
	cbmc_actiont action;
	bool result;
	char var_name[100]; // variable name for querying
	unsigned char var_value; // TODO move into incremental_cbmct class and make parameterized?
	unsigned char blocking_clause_pattern;
	unsigned semaphore_identifier;
};

class incremental_cbmct {
public:
	incremental_cbmct(const char* path, unsigned semaphore_identifier = 1u);
	virtual ~incremental_cbmct();

	virtual void start(const char* c_file, const char* output_file);
	virtual bool check(); /* TODO we have to communicate data */
	virtual unsigned char query_value(const char* var_name);
	virtual unsigned char query_value(const ::std::string & var_name);
	virtual void assume_value(const char* var_name, unsigned char value);
	virtual void assume_value(const ::std::string & var_name, unsigned char value);
    virtual void clear_assumptions();
	virtual void stop();
	virtual void list_variable_names();
	virtual void analyze_unsat_core();
	virtual unsigned char query_for_bits_in_unsat_core(const char* var_name);
	virtual unsigned char query_for_bits_in_unsat_core(const ::std::string & var_name);
	virtual void extend_blocking_clause(const char* var_name, unsigned char blocking_clause_pattern, unsigned char phase_pattern);
	virtual void extend_blocking_clause(const ::std::string & var_name, unsigned char blocking_clause_pattern, unsigned char phase_pattern);
	virtual void finish_blocking_clause();

private:
	const ::std::string path;
	unsigned semaphore_identifier;
	::std::string cbmc_semaphore_name;
	::std::string local_semaphore_name;

	pthread_t cbmc_thread;
	cbmc_parameterst params;

	sem_t* cbmc_semaphore;
	sem_t* local_semaphore;

	cbmc_shmt* shared_memory;
	int shm_segment_id;
};

#endif /* CBMC_H_ */
