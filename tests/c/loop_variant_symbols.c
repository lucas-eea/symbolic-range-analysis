// A load inside a loop is a new value on each iteration: a value carried
// around the loop (highest) must not be bounded by it (highest <= p is false
// after p = 9, then p = 3). Loop-invariant symbols (n) are kept.
int running_max(int *a, int n) {
  int highest = -2147483647 - 1;
  for (int k = 0; k < n; k++) {
    int p = a[k];
    if (highest < p)
      highest = p;
  }
  return highest;
}

int count_up(int *a, int n) {
  int c = 0;
  for (int k = 0; k < n; k++)
    if (a[k] > 0)
      c = k;
  return c;
}
