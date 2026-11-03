; Checks for tests/c/loop_variant_symbols.c: at a loop header, a range must
; not mention symbols defined inside the loop (the load, v0), which are new
; values on each iteration; inside one iteration they may. Loop-invariant
; symbols (n) stay symbolic.

; CHECK-LABEL: @running_max(
; CHECK: %highest.0 = phi i32 {{.*}}, !srange ![[H0:[0-9]+]]
; CHECK: %highest.1 = phi i32 {{.*}}, !srange ![[H1:[0-9]+]]
; CHECK-LABEL: @count_up(
; CHECK: %c.0 = phi i32 {{.*}}, !srange ![[C0:[0-9]+]]
; CHECK-DAG: ![[H0]] = !{!"-2147483648", !"2147483647", !"-2147483648", !"2147483647"}
; CHECK-DAG: ![[H1]] = !{!"max(-2147483648, v0)", !"2147483647", !"-2147483648", !"2147483647"}
; CHECK-DAG: ![[C0]] = !{!"0", !"max(-1+n, 0)", !"0", !"2147483646"}
