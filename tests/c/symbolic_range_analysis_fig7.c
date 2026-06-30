// Checks that SRA correctly computes symbolic range annotations for arithmetic
// over symbolic inputs (fig. 7 from Nazaré et al., with x in [0,15]).
int fig7(int b, int x) {
    int a = 42;
    int c = b + 1;
    int v = c - x;
    if (a < b) {
        return v;
    }
    return v;
}
