#include "sympc.h"

#include "cbmc.h"

#include "../types.h"

#include <cstdlib>
#include <cstring>
#include <libgen.h>

#include <iostream>
#include <sstream>
#include <fstream>


void print_usage(::std::ostream& out, char* program_name) {
  out << "Usage: " << program_name << " <bit-index> [--keepHigherIndexCandidates|--keepHigherIndexCandidates:<k>]" << ::std::endl;
}

bool sympc_run(unsigned bit_index, unsigned max_n, incremental_cbmct& cbmc, incremental_cbmct& minisat2_cbmc, bool keepHigherIndexCandidates, unsigned keep_index, ::std::ostream& out);

int main(int argc, char* argv[]) {
  // check parameters (begin)
  if (argc < 2) {
    print_usage(::std::cerr, argv[0]);
    return EXIT_FAILURE;
  }

  int tmp_bit_index = atoi(argv[1]);

  if (tmp_bit_index < 0 || tmp_bit_index >= 32) {
    ::std::cerr << "Invalid bit index " << tmp_bit_index << " (valid range: [0, 31])" << ::std::endl;

    print_usage(::std::cerr, argv[0]);
    return EXIT_FAILURE;
  }


  ::std::stringstream basedir_strstr;
  basedir_strstr << dirname(argv[0]) << "/..";
  char* BASEDIR = new char[basedir_strstr.str().length() + 1];
  ::std::strcpy(BASEDIR, basedir_strstr.str().c_str());


  unsigned bit_index = (unsigned)tmp_bit_index;
  bool keepHigherIndexCandidates = false;
  unsigned keep_index = 32; // TODO keep_index is not correct!!!!

  for (int i = 2; i < argc; i++) {
    if (strcmp(argv[i], "--keepHigherIndexCandidates") == 0) {
      keepHigherIndexCandidates = true;
    }
    else if (strncmp(argv[i], "--keepHigherIndexCandidates:", 28) == 0) {
        ::std::string str = ::std::string(argv[i]).substr(28);

        keep_index = atoi(str.c_str());
    }
    else {
      ::std::cerr << "Unrecognized command line argument: " << argv[i] << ::std::endl;

      print_usage(::std::cerr, argv[0]);
      return EXIT_FAILURE;
    }
  }
  // check parameters (end)


  incremental_cbmct inc_cbmc("../../cbmc-4.9-src/cbmc-4.9-incremental/src/cbmc/cbmc", 21);
  incremental_cbmct minisat2_cbmc("../../cbmc-4.9-src/cbmc-4.9-incremental-minisat-2.2.0/src/cbmc/cbmc", 20);

  bool synthesis_successful = sympc_run(bit_index, 8, inc_cbmc, minisat2_cbmc, keepHigherIndexCandidates, keep_index, ::std::cout);

  if (synthesis_successful) {
    ::std::cout << "Synthesis successful!" << ::std::endl;
    ::std::cout << "TODO: synthesize g!" << ::std::endl;
    return EXIT_SUCCESS;
  }
  else {
    ::std::cout << "Synthesis failed!" << ::std::endl;
    return EXIT_FAILURE;
  }
}

void write_run_variables_declarations(unsigned n, unsigned idx, ::std::ostream& encoding_c) {
    // variables used for the separate runs
    encoding_c << "  " << "// variables for run " << idx << ::std::endl;
    encoding_c << "  " << "unsigned char" << " x" << idx << ";" << ::std::endl;
    if (n > 1)
    {
        encoding_c << "  " << "unsigned char" << " z" << idx << "[" << (n - 1) << "];" << ::std::endl;
    }
    encoding_c << "  " << "_Bool" << " o" << idx << "[" << n << "];" << ::std::endl << ::std::endl;
}

void write_h_call(unsigned n, unsigned idx, ::std::ostream& out) {
    if (n == 1)
    {
        out << "  " << "o" << idx << "[0] = f(x" << idx << ", y1);" << ::std::endl;
    }
    else {
        out << "  " << "z" << idx << "[" << (n - 2) << "] = h" << n << "(";
        for (unsigned i = 0; i < n - 1; i++)
        {
            if (i > 0)
            {
                out << ", ";
            }
            out << "o" << idx << "[" << i << "]";
        }
        out << ");" << ::std::endl;
        out << "  " << "o" << idx << "[" << (n - 1) << "] = f(x" << idx << ", z" << idx << "[" << (n - 2) << "]);" << ::std::endl;
    }
}

void write_check(unsigned n, unsigned bit_index, ::std::ostream& out)
{
    out << "  " << "// check whether conflicting classifications exist" << ::std::endl;
    out << "  " << "if (((x0 >> " << bit_index << ") & 0x1) != ((x1 >> " << bit_index << ") & 0x1)) {" << ::std::endl;
    out << "    " << "_Bool outputs_differ = 0;" << ::std::endl << ::std::endl;

    for (unsigned i = 0; i < n; i++)
    {
        out << "    " << "outputs_differ = outputs_differ || (o0[" << i << "] != o1[" << i << "]);" << ::std::endl;
    }
    out << ::std::endl;

    out << "    " << "unsigned char validation;" << ::std::endl;
    out << "    " << "unsigned char condition;" << ::std::endl << ::std::endl;

    out << "    " << "if (validation) {" << ::std::endl;
    out << "      " << "condition = outputs_differ;" << ::std::endl;
    out << "    " << "} else {" << ::std::endl;
    out << "      " << "condition = !outputs_differ;" << ::std::endl;
    out << "    " << "}" << ::std::endl << ::std::endl;

    out << "    " << "assert(condition);" << ::std::endl;
    out << "  " << "}" << ::std::endl << ::std::endl;
}

void write_h_definition(unsigned n /* actually n - 1, it starts with 0 */, ::std::ostream& out)
{
    unsigned nr_entries = (1u << n);
    unsigned size_of_b_type = 1; // sizeof(b_type)

    // function definition
    out << "unsigned char" << " h" << (n + 1) << "(";
    for (unsigned j = 0; j < n; j++)
    {
        if (j > 0)
        {
            out << ", ";
        }
        out << "_Bool" << " o" << j;
    }
    out << ") {" << ::std::endl;
    if (nr_entries == 1u)
    {
        out << "  return h1_value_1;" << ::std::endl;
    }
    else
    {
        out << "  " << "unsigned char" << " ret = 0x";
        for (unsigned z = 0; z < size_of_b_type; z++)
        {
            out << "ff";
        }
        out << ";" << ::std::endl;

        for (unsigned z = 0; z < (size_of_b_type * 8); z++)
        {
            out << "  ret = ret & (~(g_" << (n + 1) << "(";
            for (unsigned j = 1; j <= nr_entries; j++)
            {
                out << "h" << (n + 1) << "_value_" << j << ", ";
            }
            out << z;
            for (unsigned j = 0; j < n; j++)
            {
                out << ", o" << j;
            }
            out << ") << " << z << "));" << ::std::endl;
        }
        out << "  return ret;" << ::std::endl;
    }

    out << "}" << ::std::endl;
}

void sympc_write_C_file(unsigned n, unsigned bit_index, ::std::string& c_file, ::std::string& validation_mode_variable, ::std::ostream& out, ::std::string indent) {
    validation_mode_variable = "c::foo::1::1::validation!0@1#1";

    ::std::stringstream c_file_stream;
    c_file_stream << "encoding." << n << ".c";

    c_file = c_file_stream.str();

    out << indent << "Write to file " << c_file << ::std::endl;

    ::std::ofstream encoding_c;
	encoding_c.open(c_file.c_str());

    // includes
    encoding_c << "#include \"f.c\"" << ::std::endl;
    encoding_c << "#include \"h.c\"" << ::std::endl << ::std::endl;

    // main function
    encoding_c << "void foo() {" << ::std::endl;

    // initialize h functions
    encoding_c << "  init_h();" << ::std::endl << ::std::endl;

    // variables used for the separate runs
    write_run_variables_declarations(n, 0, encoding_c);
    write_run_variables_declarations(n, 1, encoding_c);

    // experimental
    // TODO keep_index is not correct!!!!
    encoding_c << "  " << "if (!(x0 & 0x80u)) return;" << ::std::endl;
    encoding_c << "  " << "if (!(x0 & 0x80u)) return;" << ::std::endl;
    //encoding_c << "  " << "if ((x0 & 0x80u) != (x1 & 0x80u)) return;" << ::std::endl;
    //encoding_c << "  " << "if ((x0 & 0x40u) != (x1 & 0x40u)) return;" << ::std::endl;

    encoding_c << "  " << "unsigned char" << " y1;" << ::std::endl;
    encoding_c << "  " << "y1 = h1();" << ::std::endl << ::std::endl;

    // run for X0
    for (unsigned i = 1; i <= n; i++) {
      write_h_call(i, 0, encoding_c);
    }
    encoding_c << ::std::endl;

    // run for X1
    for (unsigned i = 1; i <= n; i++) {
      write_h_call(i, 1, encoding_c);
    }
    encoding_c << ::std::endl;

    // check
    write_check(n, bit_index, encoding_c);

    encoding_c << "}" << ::std::endl << ::std::endl;

    encoding_c.close();


    // write h.c file
    ::std::ofstream h_c;
    h_c.open("h.c");

    // write variables that will be used to encode the function definitions
    for (unsigned i = 0; i < n; i++)
    {
        unsigned nr_entries = (1u << i);
        for (unsigned j = 1; j <= nr_entries; j++)
        {
            h_c << "unsigned char" << " h" << (i + 1) << "_value_" << j << ";" << ::std::endl;
        }

        h_c << ::std::endl;
    }

    // write initialization code
    h_c << "unsigned char" << " rand() {" << ::std::endl;
    h_c << "  " << "unsigned char" << " tmp;" << ::std::endl;
    h_c << "  " << "return tmp;" << ::std::endl;
    h_c << "}" << ::std::endl << ::std::endl;

    h_c << "void init_h() {" << ::std::endl;

    for (unsigned i = 0; i < n; i++)
    {
        unsigned nr_entries = (1u << i);
        for (unsigned j = 1; j <= nr_entries; j++)
        {
            h_c << "  " << "h" << (i + 1) << "_value_" << j << " = rand();" << ::std::endl;
        }

        h_c << ::std::endl;
    }

    h_c << "}" << ::std::endl << ::std::endl;

    // write function definitions
    for (unsigned i = 0; i < n; i++) {
        write_g_n(i, h_c);
    }

    for (unsigned i = 0; i < n; i++) {
        write_h_definition(i, h_c);
    }

    h_c.close();
}

unsigned char* initialize_function_definitions(unsigned bit_index, unsigned n, bool keepHigherIndexCandidates, unsigned keep_index)
{
    unsigned nr_entries = 0;
    for (unsigned i = 0; i < n; i++)
    {
        nr_entries += (1u << i);
    }

    unsigned char* function_definitions = new unsigned char[nr_entries];

    // pre-initialize function definitions
    for (unsigned i = 0; i < nr_entries; i++)
    {
        function_definitions[i] = 0; //(unsigned char)(rand() % 256);
    }

    if (keepHigherIndexCandidates)
    {
        if (keep_index < 7)
        {
            function_definitions[0] = 127;
        }

        for (unsigned i = 6, counter = 1, offset = 192, delta = 128; i > keep_index && counter < nr_entries; i--)
        {
            unsigned tmp_diff = 6 - i;
            unsigned tmp_nr_entries = (1u << (tmp_diff + 1));

            for (unsigned j = 0; j < tmp_nr_entries; j++)
            {
                function_definitions[counter] = offset - (delta * j);

                counter++;
            }

            offset += (32 >> tmp_diff);
            delta >>= 1;
        }
    }

    return function_definitions;
}

void create_blocking_clause(incremental_cbmct& minisat2_cbmc, incremental_cbmct& cbmc, const ::std::string& validation_mode_variable, unsigned n, unsigned char* function_definitions, const ::std::string& x0_variable, unsigned char x0, const ::std::string& x1_variable, unsigned char x1)
{
    // create unsatisfiable formula
    minisat2_cbmc.clear_assumptions(); // TODO we should have something like update_assumption to replace only very specific values

    // create unsatisfiable instance
    minisat2_cbmc.assume_value(validation_mode_variable, 0);

    // initialize values of h_.._value variables
    for (unsigned i = 0, counter = 0; i < n; i++)
    {
        unsigned nr_local_entries = (1u << i);

        for (unsigned j = 0; j < nr_local_entries; j++)
        {
            ::std::stringstream strstr;
            strstr << "c::h" << (i + 1) << "_value_" << (j + 1) << "#2";

            minisat2_cbmc.assume_value(strstr.str(), function_definitions[counter]);
            counter++;
        }
    }

    minisat2_cbmc.assume_value(x0_variable, x0);
    minisat2_cbmc.assume_value(x1_variable, x1);

    bool unsat = !minisat2_cbmc.check();

    assert(unsat);

    minisat2_cbmc.analyze_unsat_core();

    // blocking clause
    for (unsigned i = 0, counter = 0; i < n; i++)
    {
        unsigned nr_local_entries = (1u << i);

        for (unsigned j = 0; j < nr_local_entries; j++)
        {
            ::std::stringstream strstr;
            strstr << "c::h" << (i + 1) << "_value_" << (j + 1) << "#2";

            unsigned char pattern = minisat2_cbmc.query_for_bits_in_unsat_core(strstr.str());
            unsigned char inverted = ~function_definitions[counter];

            ::std::cout << "    pattern " << (long) pattern << ::std::endl;
            ::std::cout << "    inverted " << (long) inverted << ::std::endl;

            cbmc.extend_blocking_clause(strstr.str(), pattern, inverted);

            counter++;
        }
    }

    cbmc.finish_blocking_clause();
}

bool sympc_run(unsigned bit_index, unsigned max_n, incremental_cbmct& cbmc, incremental_cbmct& minisat2_cbmc, bool keepHigherIndexCandidates, unsigned keep_index, ::std::ostream& out) {

    unsigned global_loop_counter = 0;

    ::std::string x0_variable { "c::foo::1::x0!0@1#1" };
    ::std::string x1_variable { "c::foo::1::x1!0@1#1" };

    // synthesis loop
    for (unsigned n = 1; n <= max_n; n++)
    {
        out << "Starting synthesis for n=" << n << ::std::endl;

        unsigned local_loop_counter = 0;

        // write C program
        ::std::string validation_mode_variable;
        ::std::string c_file;
        sympc_write_C_file(n, bit_index, c_file, validation_mode_variable, out, "  ");

        cbmc.start(c_file.c_str(), "cbmc.out");

        //minisat2_cbmc.start(c_file.c_str(), "cbmc-minisat.out");

        unsigned char* function_definitions = initialize_function_definitions(bit_index, n, keepHigherIndexCandidates, keep_index);

        // CEGIS loop
        while (true) {
		    local_loop_counter++;
			global_loop_counter++;
			out << "  Starting " << local_loop_counter << ". synthesis loop (" << global_loop_counter << ")" << ::std::endl;

            // validation
            cbmc.clear_assumptions();
            cbmc.assume_value(validation_mode_variable, 1);

            // initialize values of h_.._value variables
            for (unsigned i = 0, counter = 0; i < n; i++) {
                unsigned nr_local_entries = (1u << i);

                for (unsigned j = 0; j < nr_local_entries; j++) {
                    ::std::stringstream strstr;
                    strstr << "c::h" << (i + 1) << "_value_" << (j + 1) << "#2";

                    cbmc.assume_value(strstr.str(), function_definitions[counter]);
                    counter++;
                }
            }

            bool validation_succeeded = !cbmc.check();

            if (validation_succeeded) {
                cbmc.stop();
                //minisat2_cbmc.stop();

                delete[] function_definitions;

                // synthesized functions are good
                return true;
            }

            // read values for counterexamples
            unsigned char x0 = cbmc.query_value(x0_variable);
            unsigned char x1 = cbmc.query_value(x1_variable);

            ::std::cout << "    " << "CEX: x0 = " << (long) x0 << ", x1 = " << (long) x1 <<::std::endl;


            //create_blocking_clause(minisat2_cbmc, cbmc, validation_mode_variable, n, function_definitions, x0_variable, x0, x1_variable, x1);
            create_blocking_clause(cbmc, cbmc, validation_mode_variable, n, function_definitions, x0_variable, x0, x1_variable, x1);


            // synthesis
            cbmc.clear_assumptions();
            cbmc.assume_value(validation_mode_variable, 0);

            if (keepHigherIndexCandidates)
            {
                if (keep_index < 7)
                {
                    cbmc.assume_value("c::h1_value_1#2", 127);
                }
                if (keep_index < 6)
                {
                    cbmc.assume_value("c::h2_value_1#2", 192);
                    cbmc.assume_value("c::h2_value_2#2", 64);
                }
                if (keep_index < 5)
                {
                    cbmc.assume_value("c::h3_value_1#2", 224);
                    cbmc.assume_value("c::h3_value_2#2", 160);
                    cbmc.assume_value("c::h3_value_3#2", 96);
                    cbmc.assume_value("c::h3_value_4#2", 32);
                }
                if (keep_index < 4)
                {
                    for (unsigned i = 0; i < 16; i++)
                    {
                        ::std::stringstream strstr;
                        strstr << "c::h4_value_" << (i + 1) << "#2";
                        cbmc.assume_value(strstr.str(), (240 - i * 32));
                    }
                }
                if (keep_index < 3)
                {
                    for (unsigned i = 0; i < 16; i++)
                    {
                        ::std::stringstream strstr;
                        strstr << "c::h5_value_" << (i + 1) << "#2";
                        cbmc.assume_value(strstr.str(), (248 - i * 16));
                    }
                }
                if (keep_index < 2)
                {
                    for (unsigned i = 0; i < 32; i++)
                    {
                        ::std::stringstream strstr;
                        strstr << "c::h6_value_" << (i + 1) << "#2";
                        cbmc.assume_value(strstr.str(), (252 - i * 8));
                    }
                }
                if (keep_index < 1)
                {
                    for (unsigned i = 0; i < 64; i++)
                    {
                        ::std::stringstream strstr;
                        strstr << "c::h7_value_" << (i + 1) << "#2";
                        cbmc.assume_value(strstr.str(), (254 - i * 4));
                    }
                }
                if (keep_index < 0)   // won't happen, but I added it for documentation of values
                {
                    for (unsigned i = 0; i < 128; i++)
                    {
                        ::std::stringstream strstr;
                        strstr << "c::h8_value_" << (i + 1) << "#2";
                        cbmc.assume_value(strstr.str(), (255 - i * 2));
                    }
                }
            }

            bool synthesis_suceeded = cbmc.check();

            if (synthesis_suceeded) {
                // extract new candidate
                for (unsigned i = 0, counter = 0; i < n; i++)
                {
                    unsigned nr_local_entries = (1u << i);

                    for (unsigned j = 0; j < nr_local_entries; j++)
                    {
                        ::std::stringstream strstr;
                        strstr << "c::h" << (i + 1) << "_value_" << (j + 1) << "#2";

                        function_definitions[counter] = cbmc.query_value(strstr.str());

                        ::std::cout << "    " << "new candidate h" << (i + 1) << "_value_" << (j + 1) << " = " << (long) function_definitions[counter] << ::std::endl;

                        counter++;
                    }
                }
            }
            else {
                // no further candidate can be found
                break;
            }
		}

		cbmc.stop();
		//minisat2_cbmc.stop();

		delete[] function_definitions;
    }

    return false;
}

