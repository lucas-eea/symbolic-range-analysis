// Unsigned comparisons and values computed before the branch. Below
// i <= j && j < i + 10 && i < 1000000, i is in [0, 999999] (i < 1000000
// unsigned, with 1000000 non-negative), so i + 10 does not wrap on that edge,
// j is in [0, i + 9], and j - i is in [0, 9]: the symbol i cancels.
unsigned f(unsigned i, unsigned j) {
  if (i <= j && j < i + 10 && i < 1000000)
    return (j - i) / 3;
  return 0;
}
