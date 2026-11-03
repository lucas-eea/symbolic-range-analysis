#include <stdio.h>

void foo(const int M, const int N, const int P) {
    if (P > N) {
        if (N > M) {
            if (M > P) {
                printf("Dumb as a post\n");
            }
        }
    }
}
