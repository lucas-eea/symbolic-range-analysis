; Checks for tests/c/guard_facts.c: conditions on symbols (sigma nodes) are
; facts in the blocks they dominate, and simplify bounds there.

; CHECK-LABEL: @guarded(
; CHECK: %sub = sub nsw i32 %n.t, 1, !srange ![[SUB:[0-9]+]]
; CHECK: %cond = phi i32 {{.*}}, !srange ![[COND:[0-9]+]]
; CHECK: %retval.0 = phi i32 {{.*}}, !srange ![[RET:[0-9]+]]
; CHECK-LABEL: @small(
; CHECK: %add = add nsw i32 %x.t.t, 0, !srange ![[SMALL:[0-9]+]]
; CHECK-DAG: ![[SUB]] = !{!"-1+n", !"-1+n", !"0", !"2147483646"}
; CHECK-DAG: ![[COND]] = !{!"0", !"-1+n", !"0", !"2147483646"}
; CHECK-DAG: ![[RET]] = !{!"0", !"max(-1+n, 0)", !"0", !"2147483646"}
; CHECK-DAG: ![[SMALL]] = !{!"x", !"x", !"0", !"255"}
