; Checks for tests/c/transitive_dependences_handling.c through ESSAfier + SRA.
; Bounds that combine min/max with arithmetic must be kept, not collapsed:
; arithmetic is pushed inside min/max, and multiplying by a constant scales
; both bounds.

; CHECK: %mul = mul nsw i32 %add, 2, !srange ![[MUL:[0-9]+]]
; CHECK: %add.t = add nsw i32 %a.t, 1, !srange ![[ADDT:[0-9]+]]
; CHECK: %add1 = add nsw i32 %mul.t, 1, !srange ![[ADD1:[0-9]+]]
; CHECK: %retval.0 = phi i32 {{.*}}, !srange ![[RET:[0-9]+]]
; CHECK-DAG: ![[MUL]] = !{!"2+2*a", !"2+2*a",
; CHECK-DAG: ![[ADDT]] = !{!"1+a", !"min(1+a, b)",
; CHECK-DAG: ![[ADD1]] = !{!"3+2*a", !"min(1+2*b, 3+2*a)",
; CHECK-DAG: ![[RET]] = !{!"min(0, 3+2*a)", !"max(0, min(1+2*b, 3+2*a))",
