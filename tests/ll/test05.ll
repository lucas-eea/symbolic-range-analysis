; Checks for tests/c/test05.c: ExactValues proves j == 3 * i after the loop,
; so sra-cvp folds 3*i != j to false and simplifycfg deletes the printf.

; CHECK-LABEL: define {{.*}} @foo(
; CHECK-NOT: @printf
; CHECK: ret void
