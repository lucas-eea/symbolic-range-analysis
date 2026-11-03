// Checks that branch conditions on symbols simplify bounds where they hold.
int guarded(int n) {
  if (n > 0) {
    int m = n - 1;        // [-1+n, -1+n], numerically [0, 2147483646]
    int k = m > 0 ? m : 0; // max(0, -1+n) simplifies to -1+n here
    return k;
  }
  return 0;
}

unsigned char small(int x) {
  if (x >= 0 && x < 256)
    return x + 0;          // x is in [0, 255] here: numerically 8 bits
  return 0;
}
