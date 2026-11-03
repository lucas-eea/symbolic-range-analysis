; Checks for tests/c/narrowing_loops.c: widening sends the loop counter to
; +inf; narrowing (and e-SSA renaming of every dominated use) recovers it.

; CHECK-LABEL: @sum_const(
; CHECK: %i.0 = phi i32 {{.*}}, !srange ![[CH:[0-9]+]]
; CHECK: %i.0.t = phi i32 {{.*}}, !srange ![[CB:[0-9]+]]
; CHECK: %inc = add nsw i32 %i.0.t, 1, !srange ![[CI:[0-9]+]]
; CHECK: %i.0.f = phi i32 {{.*}}, !srange ![[CE:[0-9]+]]
; CHECK-LABEL: @sum_sym(
; CHECK: %i.0 = phi i32 {{.*}}, !srange ![[SH:[0-9]+]]
; CHECK: %i.0.t = phi i32 {{.*}}, !srange ![[SB:[0-9]+]]
; CHECK: %i.0.f = phi i32 {{.*}}, !srange ![[SE:[0-9]+]]
; CHECK-DAG: ![[CH]] = !{!"0", !"200", !"0", !"200"}
; CHECK-DAG: ![[CB]] = !{!"0", !"199", !"0", !"199"}
; CHECK-DAG: ![[CI]] = !{!"1", !"200", !"1", !"200"}
; CHECK-DAG: ![[CE]] = !{!"200", !"200", !"200", !"200"}
; CHECK-DAG: ![[SH]] = !{!"0", !"max(0, n)", !"0", !"2147483647"}
; CHECK-DAG: ![[SB]] = !{!"0", !"-1+n", !"0", !"2147483646"}
; CHECK-DAG: ![[SE]] = !{!"max(0, n)", !"max(0, n)", !"0", !"2147483647"}
