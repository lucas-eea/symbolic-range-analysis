; Checks for tests/c/loops_and_widening.c.

; CHECK-LABEL: @ne_loop(
; CHECK: %i.0 = phi i32 {{.*}}, !srange ![[NE:[0-9]+]]
; CHECK: %inc = add nsw i32 %i.0.t, 1, !srange ![[NEINC:[0-9]+]]
; CHECK-LABEL: @down(
; CHECK: %i.0 = phi i32 {{.*}}, !srange ![[DOWN:[0-9]+]]
; CHECK: %i.0.t = phi i32 {{.*}}, !srange ![[DOWNB:[0-9]+]]
; CHECK: %i.0.f = phi i32 {{.*}}, !srange ![[DOWNE:[0-9]+]]
; CHECK-LABEL: @dowhile(
; CHECK: %i.0 = phi i32 {{.*}}, !srange ![[DW:[0-9]+]]
; CHECK: %add1 = add i32 %i.0, 1, !srange ![[DWI:[0-9]+]]
; CHECK: %add1.f = phi i32 {{.*}}, !srange ![[DWE:[0-9]+]]
; CHECK-LABEL: @widen_unknown(
; CHECK: %conv = sext i32 %mul to i64, !srange ![[W:[0-9]+]]
; CHECK-DAG: ![[NE]] = !{!"0", !"max(0, n)", !"0", !"2147483647"}
; CHECK-DAG: ![[NEINC]] = !{!"1", !"max(1, 1+n)", !"1", !"2147483647"}
; CHECK-DAG: ![[DOWN]] = !{!"min(0, n)", !"n", !"-2147483648", !"2147483647"}
; CHECK-DAG: ![[DOWNB]] = !{!"1", !"n", !"1", !"2147483647"}
; CHECK-DAG: ![[DOWNE]] = !{!"min(0, n)", !"min(0, n)", !"-2147483648", !"0"}
; CHECK-DAG: ![[DW]] = !{!"0", !"99", !"0", !"99"}
; CHECK-DAG: ![[DWI]] = !{!"1", !"100", !"1", !"100"}
; CHECK-DAG: ![[DWE]] = !{!"100", !"100", !"100", !"100"}
; CHECK-DAG: ![[W]] = !{!"-2147483648", !"2147483647", !"-2147483648", !"2147483647"}
