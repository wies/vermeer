#include <stdio.h>

int main(int argc, char** argv){
    int x = 0xFFFF;
    *(char*) &x = 0xFF;
    printf("%d\n", x);
}
