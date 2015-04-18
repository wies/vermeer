#include "cbmc.h"

#include <iostream>

#include <cstdlib>

void run(incremental_cbmct& inc_cbmc) {
    bool result = inc_cbmc.check();

    if (result) {
        ::std::cout << "SAT" << ::std::endl;

        //inc_cbmc.list_variable_names();

        unsigned char x = inc_cbmc.query_value("c::foo::1::x!0@1#1");
        unsigned char y = inc_cbmc.query_value("c::foo::1::y!0@1#1");

        ::std::cout << " x = " << (long)x << ::std::endl;
        ::std::cout << " y = " << (long)y << ::std::endl;
    }
    else {
        ::std::cout << "UNSAT" << ::std::endl;

        inc_cbmc.analyze_unsat_core();

        unsigned char x = inc_cbmc.query_for_bits_in_unsat_core("c::foo::1::x!0@1#1");
        unsigned char y = inc_cbmc.query_for_bits_in_unsat_core("c::foo::1::y!0@1#1");

        ::std::cout << " x = " << (long)x << ::std::endl;
        ::std::cout << " y = " << (long)y << ::std::endl;
    }
}

int main(int argc, char* argv[]) {

    incremental_cbmct inc_cbmc("../../cbmc-4.9-src/cbmc-4.9-incremental/src/cbmc/cbmc");

    inc_cbmc.start("test.c", "test.out");

    run(inc_cbmc);

    inc_cbmc.assume_value("c::foo::1::x!0@1#1", 4);

    run(inc_cbmc);

    inc_cbmc.clear_assumptions();

    inc_cbmc.assume_value("c::foo::1::x!0@1#1", 7);

    run(inc_cbmc);

    inc_cbmc.clear_assumptions();

    inc_cbmc.assume_value("c::foo::1::x!0@1#1", 7);
    inc_cbmc.assume_value("c::foo::1::y!0@1#1", 7);

    run(inc_cbmc);

    inc_cbmc.clear_assumptions();

    inc_cbmc.assume_value("c::foo::1::x!0@1#1", 0);
    inc_cbmc.assume_value("c::foo::1::y!0@1#1", 100);

    run(inc_cbmc);

    inc_cbmc.clear_assumptions();

    inc_cbmc.assume_value("c::foo::1::x!0@1#1", 6);
    inc_cbmc.assume_value("c::foo::1::y!0@1#1", 6);

    run(inc_cbmc);

    inc_cbmc.clear_assumptions();
    run(inc_cbmc);

    inc_cbmc.clear_assumptions();

    unsigned char blocking_clause_pattern = 255;
    unsigned char phase_pattern = 6;
    phase_pattern = ~phase_pattern;

    ::std::cout << "blocking: " << (long)blocking_clause_pattern << ", " << (long)phase_pattern << ::std::endl;

    inc_cbmc.extend_blocking_clause("c::foo::1::x!0@1#1", blocking_clause_pattern, phase_pattern);
    inc_cbmc.finish_blocking_clause();

    phase_pattern = 4;
    phase_pattern = ~phase_pattern;

    ::std::cout << "blocking: " << (long)blocking_clause_pattern << ", " << (long)phase_pattern << ::std::endl;

    inc_cbmc.extend_blocking_clause("c::foo::1::x!0@1#1", blocking_clause_pattern, phase_pattern);
    inc_cbmc.finish_blocking_clause();

    run(inc_cbmc);

    inc_cbmc.stop();

    return EXIT_SUCCESS;
}
