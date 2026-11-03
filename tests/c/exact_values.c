// Linear equalities between variables (ExactValues): after the loops,
// j == 3 * i, which intervals cannot express. Both comparisons are false.
void use(int);

void two_loops(int n) {
  int i, j = 0;
  for (i = 0; i < n; ++i)
    j += 3;
  while (i < 3 * n) {
    i++;
    j += 3;
  }
  int bad = 3 * i != j;
  use(bad);
}

void two_params(int m, int n) {
  int i, j = 0;
  for (i = 0; i < m; ++i)
    j += 3;
  while (i < n) {
    i++;
    j += 3;
  }
  int bad = 3 * i != j;
  use(bad);
}

// The step of i depends on a branch, but j always changes by 3 times as
// much: j - 3 * i stays 0. Decided (false).
void irregular(int n) {
  int i, j = 0;
  for (i = 0; i < n; ++i) {
    j += 3;
    if (n % 2) {
      i++;
      j += 3;
    }
  }
  int unknown = 3 * i != j;
  use(unknown);
}

// Not decided: unsigned arithmetic may wrap, so it is not exact.
void wrapping(unsigned n) {
  unsigned i, j = 0;
  for (i = 0; i < n; ++i)
    j += 3;
  int unknown = 3 * i != j;
  use(unknown);
}

// Both loops run max(n, 0) times: i leaves the first at max(0, n) and the
// second at max(2n, max(0, n)); j == k in every case of the sign of n.
// Decided (false).
void equal_trips(int n) {
  int i, j = 0, k = 0;
  for (i = 0; i < n; ++i)
    j += 2;
  for (; i < 2 * n; ++i)
    k += 2;
  int bad = j != k;
  use(bad);
}

// Not decided: the second loop runs once more when n >= 0 (j != k then),
// but not when n < 0.
void unequal_trips(int n) {
  int i, j = 0, k = 0;
  for (i = 0; i < n; ++i)
    j += 2;
  for (; i < 2 * n + 1; ++i)
    k += 2;
  int unknown = j != k;
  use(unknown);
}

// Not decided: with a step of 2, i may leave the loop above n.
void stride2(int n) {
  int i;
  for (i = 0; i < n; i += 2)
    ;
  int unknown = i != n;
  use(unknown);
}
