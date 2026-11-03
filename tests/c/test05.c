#include <stdio.h>

void foo(const int N) {
    int i;
    int j = 0;
    for (i = 0; i < N; ++i) {
        j += 3;
        if (N % 2) {
            i++;
            j += 3;
        }
    }
    if (3*i != j) {
        printf("Dumb as a post\n");
    }
}
