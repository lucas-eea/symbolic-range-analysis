// Checks loop bounds derived from exit tests (!= and decreasing loops), the
// deferred wraparound guard on an unsigned bottom-tested loop, and that a
// sign extension keeps the limits of its source type.
int ne_loop(int *p, int n) {        // i in [0, max(0, n)] at the header
  int s = 0;
  for (int i = 0; i != n; i++)
    s += p[i];
  return s;
}

int down(int *p, int n) {           // i in [min(0, n), n] at the header
  int s = 0;
  for (int i = n; i > 0; i--)
    s += p[i];
  return s;
}

unsigned dowhile(unsigned *p) {     // i in [0, 99] (i + 1 in [1, 100])
  unsigned i = 0, s = 0;
  do {
    s += p[i];
    i = i + 1;
  } while (i < 100);
  return s;
}

long widen_unknown(unsigned x) {    // the i32 may wrap; its sext is still i32
  int y = x * 7u;
  return y;
}
