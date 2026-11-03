; Checks for tests/c/test08.c: P > N and N > M give M <= P - 2, so sra-cvp
; folds M > P to false and simplifycfg deletes the printf.

; CHECK-LABEL: define {{.*}} @foo(
; CHECK-NOT: @printf
; CHECK: ret void
