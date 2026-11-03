; Checks for tests/c/unsigned_window.c (run after SimplifyCFG, which turns
; the && chain into one branch on a logical and).

; CHECK-LABEL: @f(
; CHECK: %i.t = phi i32 {{.*}}, !srange ![[I:[0-9]+]]
; CHECK: %sub = sub i32 %j.t, %i.t, !srange ![[SUB:[0-9]+]]
; CHECK: %div = udiv i32 %sub, 3, !srange ![[DIV:[0-9]+]]
; CHECK-DAG: ![[I]] = !{!"max(0, i)", !"min(999999, i, j)", !"0", !"999999"}
; CHECK-DAG: ![[SUB]] = !{!"max(-i+j, 0)", !"min(-i+j, 9)", !"0", !"9"}
; CHECK-DAG: ![[DIV]] = !{!"max(0, idiv(-i+j,3))", !"min(3, idiv(-i+j,3))", !"0", !"3"}
