// Checks casts, comparisons, bitwise operations and type bounds of symbols.
unsigned zext_char(unsigned char c) { return c; }        // [0, 255]
int sext_char_plus1(signed char c) { return c + 1; }     // [c+1, c+1] in [-127, 128]
int low_bits(int x) { return x & 15; }                   // [0, 15]
int shift_right(unsigned x) { return x >> 28; }          // [0, 15]
int is_less(int a, int b) { return a < b; }              // zext of an i1: [0, 1]
short trunc_small(int x) { return (short)(x & 255); }    // fits: [0, 255]
int pick(int c, int a) { return c ? a : 7; }             // [min(7, a), max(7, a)]
