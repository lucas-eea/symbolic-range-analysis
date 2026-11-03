// Checks that narrowing recovers loop bounds after widening: with a constant
// bound (i in [0, 199] in the body, [0, 200] at the header) and with a
// symbolic bound n.
int sum_const(int *p) {
  int s = 0;
  for (int i = 0; i < 200; i++)
    s += p[i];
  return s;
}

int sum_sym(int *p, int n) {
  int s = 0;
  for (int i = 0; i < n; i++)
    s += p[i];
  return s;
}
