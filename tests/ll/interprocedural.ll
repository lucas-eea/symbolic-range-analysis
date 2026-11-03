; Checks for tests/c/interprocedural.c: parameters of functions whose every
; call is known are bounded by their call sites (numerically, and by the
; less-than relation of OOPSLA'14 Fig. 19); exported functions are not.

; CHECK-LABEL: define internal i32 @get(
; CHECK-SAME: !srange.args ![[GETARGS:[0-9]+]]
; CHECK: %sub = sub nsw i32 %n, %i, !srange ![[GETSUB:[0-9]+]]
; CHECK-LABEL: define internal i32 @twice(
; CHECK-SAME: !srange.args ![[TWARGS:[0-9]+]]
; CHECK: %mul = mul nsw i32 %x, 2, !srange ![[TWMUL:[0-9]+]]
; CHECK-LABEL: define dso_local i32 @exported(
; CHECK: %mul = mul nsw i32 %x, 2, !srange ![[EXMUL:[0-9]+]]
; CHECK-LABEL: define internal i32 @clamp(
; CHECK: %cond = phi i32 {{.*}}, !srange ![[CLAMP:[0-9]+]]
; CHECK-DAG: ![[GETARGS]] = !{![[NOARG:[0-9]+]], ![[GETI:[0-9]+]], ![[GETN:[0-9]+]]}
; CHECK-DAG: ![[NOARG]] = !{}
; CHECK-DAG: ![[GETI]] = !{!"i", !"i", !"0", !"99"}
; CHECK-DAG: ![[GETN]] = !{!"n", !"n", !"100", !"100"}
; CHECK-DAG: ![[GETSUB]] = !{!"-i+n", !"-i+n", !"1", !"100"}
; CHECK-DAG: ![[TWARGS]] = !{![[TWX:[0-9]+]]}
; CHECK-DAG: ![[TWX]] = !{!"x", !"x", !"3", !"7"}
; CHECK-DAG: ![[TWMUL]] = !{!"2*x", !"2*x", !"6", !"14"}
; CHECK-DAG: ![[EXMUL]] = !{!"2*x", !"2*x", !"-2147483648", !"2147483647"}
; CHECK-DAG: ![[CLAMP]] = !{!"i", !"i", !"0", !"2147483646"}
