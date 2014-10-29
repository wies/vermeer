#include <stdio.h>
#include <signal.h>

void *handler(int dont_care) { return 0; }

int arr_init[] = { 0, 3, 4, 5, 6, 7, 1, 9 };

int main(int argc, char** argv) {
    typedef int MY_INT;
    struct my_struct {
        int fst_field[3];
        MY_INT snd_field;
    } local_record[2];

    int argc2 = argc;
    int* argc_ptr = &argc;
    char** argv2 = argv;
    char*** argv_ptr = &argv;

    void* vp = (void*) signal(SIGXCPU, &handler);

    int size_of_str = sizeof("abcd");
    int size_of_ull = sizeof(unsigned long long);
    int size_of_argc2 = sizeof(argc2);
    int ao1 = __alignof__(unsigned long long);
    int ao2 = __alignof__(argc2);

    if (argc == 3) vp = 0;

    char* p = 0;
    //*p = 10;

    p = "abcdef";
    char my_char = (*p+4);
    int boolean = !"abcdef";
    
    local_record[0].snd_field = 1111;
    int *ptr = &(local_record[0].snd_field);
    struct my_struct *my_struct_ptr = local_record;
    //struct my_struct struct_copy = *(my_struct_ptr + 1);
    //int *arr_ptr = struct_copy.fst_field + 1;
    //*arr_ptr = 10;
    //int val1 = *arr_ptr;
    int val2 = local_record[1].fst_field[1];
    int *last_ptr = &(local_record[1].fst_field[1]);
    printf("%d %p\n", *last_ptr, arr_init);

    int x = 9999999, y = 99;
    x++; y++;
    int *p1 = &x;
    p1++; p1--;
    int **p2 = &p1;
    x++;
    //printf("%d %d %d %d\n", *p1, *((*(p2-1+1))-1+1), *ptr, arr_init[4]);
    return 0;
}
