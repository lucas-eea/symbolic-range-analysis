; Loop bounds derived from exit tests in rotated loops (test at the bottom,
; on the incremented value), as optimized code has them.

; Vectorized-style loop: step 4, nuw only, exits when next == 31996.
define void @step4_eq() {
entry:
  br label %loop
loop:
  %i = phi i64 [ 0, %entry ], [ %next, %loop ]
  %next = add nuw i64 %i, 4
  %done = icmp eq i64 %next, 31996
  br i1 %done, label %exit, label %loop
exit:
  ret void
}
; CHECK-LABEL: @step4_eq(
; CHECK: %i = phi i64 {{.*}}, !srange ![[S4:[0-9]+]]
; CHECK: %next = add nuw i64 %i, 4, !srange ![[S4N:[0-9]+]]

; Guarded rotated loop with a symbolic bound: while (next < n). The guard
; n > 0 lets max(-1+n, 0) simplify to -1+n (guard facts).
define void @guarded_slt(i32 %n) {
entry:
  %guard = icmp sgt i32 %n, 0
  br i1 %guard, label %loop, label %exit
loop:
  %i = phi i32 [ 0, %entry ], [ %next, %loop ]
  %next = add nsw i32 %i, 1
  %more = icmp slt i32 %next, %n
  br i1 %more, label %loop, label %exit
exit:
  ret void
}
; CHECK-LABEL: @guarded_slt(
; CHECK: %i = phi i32 {{.*}}, !srange ![[G:[0-9]+]]

; Counting down by 2 with a test at the top on the phi: while (i != 0).
define void @down_ne() {
entry:
  br label %head
head:
  %i = phi i32 [ 100, %entry ], [ %next, %body ]
  %go = icmp ne i32 %i, 0
  br i1 %go, label %body, label %exit
body:
  %next = sub nsw i32 %i, 2
  br label %head
exit:
  ret void
}
; CHECK-LABEL: @down_ne(
; CHECK: %i = phi i32 {{.*}}, !srange ![[D:[0-9]+]]

; CHECK-DAG: ![[S4]] = !{!"0", !"31992", !"0", !"31992"}
; CHECK-DAG: ![[S4N]] = !{!"4", !"31996", !"4", !"31996"}
; CHECK-DAG: ![[G]] = !{!"0", !"-1+n", !"0", !"2147483646"}
; CHECK-DAG: ![[D]] = !{!"0", !"100", !"0", !"100"}
