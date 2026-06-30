// Checks that ESSAfier splits the live range of a variable v along a branch edge if
// v depends transitively on a or b from cond(a,b) and v is used in a label dominated
// by the branch target (by inserting a copy of v).
// Here x = a+1 and y = x*2 are recomputed in the true branch using the sigma for a.
int test(int a, int b) {
    int x = a + 1;   // directly depends on a
    int y = x * 2;   // transitively depends on a through x
    if (a < b) {
        int p = y + 1;
	return p;
    }
    return 0;        // false branch never touches y
}
