struct INNER { int a; int b; };
struct MY_RET { int z; struct INNER x; int y; };

struct MY_RET some_extern_fun();

int *return_a_pointer();
