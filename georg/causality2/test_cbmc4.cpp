#include "cbmc.h"

#include <iostream>

#include <cstdlib>

bool run(incremental_cbmct& inc_cbmc) {
    bool result = inc_cbmc.check();

    if (result) {
        ::std::cout << "SAT" << ::std::endl;

        inc_cbmc.list_variable_names();

        unsigned char x = inc_cbmc.query_value("c::foo::1::x!0@1#1");
        unsigned char y = inc_cbmc.query_value("c::foo::1::y!0@1#1");
        unsigned char z = inc_cbmc.query_value("c::foo::1::z!0@1#1");

        ::std::cout << " x = " << (long)x << ::std::endl;
        ::std::cout << " y = " << (long)y << ::std::endl;
        ::std::cout << " z = " << (long)z << ::std::endl;
    }
    else {
        ::std::cout << "UNSAT" << ::std::endl;

#if 0

        inc_cbmc.analyze_unsat_core();

        unsigned char x = inc_cbmc.query_for_bits_in_unsat_core("c::foo::1::x!0@1#1");
        unsigned char y = inc_cbmc.query_for_bits_in_unsat_core("c::foo::1::y!0@1#1");

        ::std::cout << " x = " << (long)x << ::std::endl;
        ::std::cout << " y = " << (long)y << ::std::endl;
#endif
    }

    return result;
}

int main(int argc, char* argv[]) {

    // two CBMC instances
    incremental_cbmct inc_cbmc("/home/andi/mpc-synthesis/cbmc-4.9-src/cbmc-4.9-incremental/src/cbmc/cbmc", 1);

    inc_cbmc.start("test4.c", "test4.out");

    ::std::string x_str { "c::foo::1::x!0@1#1" };
    ::std::string y_str { "c::foo::1::y!0@1#1" };
    ::std::string z_str { "c::foo::1::z!0@1#1" };

    ::std::string a_str { "c::foo::1::1::a!0@1#2" };
    ::std::string b_str { "c::foo::1::1::b!0@1#2" };

    ::std::string validation_str { "c::foo::1::1::validation!0@1#1" };

    unsigned char z_value = 0;

    while (true) {
        ::std::cout << "Trying z = " << (long) z_value << ::std::endl;

        inc_cbmc.clear_assumptions();

        inc_cbmc.assume_value(validation_str, 1);
        inc_cbmc.assume_value(z_str, z_value);

        if (!run(inc_cbmc))
        {
            // no counterexample was found, we are done!
            ::std::cout << "Finishing with z = " << (long) z_value << ::std::endl;
            break;
        }

        // read values for counterexamples
        unsigned char x = inc_cbmc.query_value(x_str);
        unsigned char y = inc_cbmc.query_value(y_str);


        inc_cbmc.clear_assumptions();

        // create unsatisfiable instance
        inc_cbmc.assume_value(validation_str, 0);
        inc_cbmc.assume_value(z_str, z_value);
        inc_cbmc.assume_value(x_str, x);
        inc_cbmc.assume_value(y_str, y);

        run(inc_cbmc);


        // assuming run was unsatisfiable
        inc_cbmc.analyze_unsat_core();

        unsigned char z_pattern = inc_cbmc.query_for_bits_in_unsat_core(z_str);
        unsigned char z_inverted = ~z_value;

        ::std::cout << "z pattern " << (long) z_pattern << ::std::endl;
        ::std::cout << "z inverted " << (long) z_inverted << ::std::endl;

        inc_cbmc.extend_blocking_clause(z_str, z_pattern, z_inverted);
        inc_cbmc.finish_blocking_clause();

        inc_cbmc.clear_assumptions();
        inc_cbmc.assume_value(validation_str, 0);

        if (run(inc_cbmc))
        {
            // found a new candidate
            z_value = inc_cbmc.query_value(z_str);
        }
        else {
            // no further candidate exists
            ::std::cout << "No further candidate can be found!" << ::std::endl;
            break;
        }
    }

    inc_cbmc.stop();

    return EXIT_SUCCESS;
}
