// Checks parameter bounds from call sites (static functions: every call is
// known) and the less-than relation between parameters (OOPSLA'14 Fig. 19).
static int get(int *a, int i, int n) {  // i in [0, 99], n = 100, i < n
  return a[i] + (n - i);                // n - i >= 1 by the relation
}

int caller(int *a) {
  int s = 0;
  for (int i = 0; i < 100; i++)
    s += get(a, i, 100);
  return s;
}

static int twice(int x) { return x * 2; } // x in [3, 7]: 2x in [6, 14]

int use_twice(void) { return twice(3) + twice(7); }

int exported(int x) { return x * 2; }     // may be called from anywhere

// Every call passes i < n with symbolic n: inside, i <= n - 1 holds, so
// max(i, n - 1) is n - 1 and min(i, n - 1) is i.
static int clamp(int i, int n) { return i < n ? i : n - 1; }

int sum_clamped(int *a, int n) {
  int s = 0;
  for (int i = 0; i < n; i++)
    s += a[clamp(i, n)];
  return s;
}
