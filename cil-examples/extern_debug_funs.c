#include "extern_debug_funs.h"

struct MY_RET some_extern_fun()
{
    struct MY_RET r = { 150, { 65, 66 }, 9 };
    return r;
}

int *return_a_pointer() { return 0; }
