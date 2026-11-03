; A branch on a logical and of comparisons (the select form SimplifyCFG
; gives `i < n && i < 100`) refines i with both comparisons on the true edge:
; i <= min(n - 1, 99, i). On the false edge nothing follows.

define i32 @both(i32 %i, i32 %n) {
entry:
  %c1 = icmp slt i32 %i, %n
  %c2 = icmp slt i32 %i, 100
  %and = select i1 %c1, i1 %c2, i1 false
  br i1 %and, label %then, label %else
then:
  %r = add nsw i32 %i, 0
  ret i32 %r
else:
  ret i32 0
}

; CHECK-LABEL: @both(
; CHECK: then:
; CHECK: %i.t = phi i32 [ %i, %entry ], !sigma !{{[0-9]+}}, !srange ![[T:[0-9]+]]
; CHECK: else:
; CHECK: %i.f = phi i32 [ %i, %entry ], !sigma !{{[0-9]+}}, !srange ![[F:[0-9]+]]
; CHECK-DAG: ![[T]] = !{!"i", !"min(-1+n, 99, i)",
; CHECK-DAG: ![[F]] = !{!"i", !"i",
