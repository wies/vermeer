// test C program for CBMC

void foo() {

    unsigned char x;
    unsigned char y;
    unsigned char z;

    if ((x & (1u << 7)) != (y & (1u << 7))) {
        unsigned char a = (x <= z);
        unsigned char b = (y <= z);

        unsigned char validation;
        unsigned char condition;

        if (validation) {
            condition = (a != b);
        }
        else {
            condition = (a == b);
        }

        assert(condition);
    }
}
