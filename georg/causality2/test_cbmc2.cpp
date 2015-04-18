#include "cbmc.h"

#include <iostream>

#include <cstdlib>

void run(incremental_cbmct& inc_cbmc) {
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
}

int main(int argc, char* argv[]) {

    // two CBMC instances
    incremental_cbmct inc_cbmc("../../cbmc-4.9-src/cbmc-4.9-incremental/src/cbmc/cbmc", 20);
    incremental_cbmct inc_cbmc2("../../cbmc-4.9-src/cbmc-4.9-incremental/src/cbmc/cbmc", 21);

    inc_cbmc.start("test2.c", "test.out");
    inc_cbmc2.start("test2.c", "test2.out");

    ::std::string x_str { "c::foo::1::x!0@1#1" };
    ::std::string y_str { "c::foo::1::y!0@1#1" };
    ::std::string z_str { "c::foo::1::z!0@1#1" };

    ::std::string a_str { "c::foo::1::1::a!0@1#2" };
    ::std::string b_str { "c::foo::1::1::b!0@1#2" };

    unsigned char z_value = 0;

    inc_cbmc.assume_value(z_str, z_value);

    run(inc_cbmc);


    // modifying the problem instance based on the obtained values for x and y

    inc_cbmc.clear_assumptions();

    unsigned char x = inc_cbmc.query_value(x_str);
    unsigned char y = inc_cbmc.query_value(y_str);
    unsigned char z = inc_cbmc.query_value(z_str);

    unsigned char a = inc_cbmc.query_value(a_str);

    inc_cbmc.assume_value(x_str, x);
    inc_cbmc.assume_value(y_str, y);
    inc_cbmc.assume_value(z_str, z);
    inc_cbmc.assume_value(a_str, !a);

    run(inc_cbmc);

    // assuming run was unsatisfiable
    inc_cbmc.analyze_unsat_core();

    unsigned char z_pattern = inc_cbmc.query_for_bits_in_unsat_core(z_str);
    unsigned char z_inverted = ~z_value;

    ::std::cout << "z pattern " << (long) z_pattern << ::std::endl;
    ::std::cout << "z inverted " << (long) z_inverted << ::std::endl;

    inc_cbmc.extend_blocking_clause(z_str, z_pattern, z_inverted);
    inc_cbmc.finish_blocking_clause();


    // just for test

    inc_cbmc.clear_assumptions();

    run(inc_cbmc);




    inc_cbmc.clear_assumptions();

    x = inc_cbmc.query_value(x_str);
    y = inc_cbmc.query_value(y_str);
    z = inc_cbmc.query_value(z_str);

    a = inc_cbmc.query_value(a_str);

    inc_cbmc.assume_value(x_str, x);
    inc_cbmc.assume_value(y_str, y);
    inc_cbmc.assume_value(z_str, z);
    inc_cbmc.assume_value(a_str, !a); // TODO is this correct?


    run(inc_cbmc);

    // assuming run was unsatisfiable
    inc_cbmc.analyze_unsat_core();

    z_pattern = inc_cbmc.query_for_bits_in_unsat_core(z_str);
    z_inverted = ~z_value;

    ::std::cout << "z pattern " << (long) z_pattern << ::std::endl;
    ::std::cout << "z inverted " << (long) z_inverted << ::std::endl;

    inc_cbmc.extend_blocking_clause(z_str, z_pattern, z_inverted);
    inc_cbmc.finish_blocking_clause();



    // just for test

    inc_cbmc.clear_assumptions();

    run(inc_cbmc);




    inc_cbmc.clear_assumptions();

    x = inc_cbmc.query_value(x_str);
    y = inc_cbmc.query_value(y_str);
    z = inc_cbmc.query_value(z_str);

    a = inc_cbmc.query_value(a_str);

    inc_cbmc.assume_value(x_str, x);
    inc_cbmc.assume_value(y_str, y);
    inc_cbmc.assume_value(z_str, z);
    inc_cbmc.assume_value(a_str, !a); // TODO is this correct?


    run(inc_cbmc);

    // assuming run was unsatisfiable
    inc_cbmc.analyze_unsat_core();

    z_pattern = inc_cbmc.query_for_bits_in_unsat_core(z_str);
    z_inverted = ~z_value;

    ::std::cout << "z pattern " << (long) z_pattern << ::std::endl;
    ::std::cout << "z inverted " << (long) z_inverted << ::std::endl;

    inc_cbmc.extend_blocking_clause(z_str, z_pattern, z_inverted);
    inc_cbmc.finish_blocking_clause();

    inc_cbmc.stop();
    inc_cbmc2.stop();

    return EXIT_SUCCESS;
}
