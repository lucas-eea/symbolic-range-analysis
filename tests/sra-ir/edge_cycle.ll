; On the exit edge of `i + 1 == n`, n and i + 1 refine each other. Their
; sigma nodes must not read each other's stored states: the fixpoint
; iteration starts with i + 1 in [1, 1], and the two would confirm that
; forever, giving n in [1, 1] after the loop (seed_chase in oggenc).

define i64 @count(i64 %n) {
entry:
  %pos = icmp sgt i64 %n, 0
  br i1 %pos, label %loop, label %none
loop:
  %i = phi i64 [ 0, %entry ], [ %inc, %loop ]
  %inc = add nuw nsw i64 %i, 1
  %done = icmp eq i64 %inc, %n
  br i1 %done, label %after, label %loop
after:
  %r = add nsw i64 %n, 0
  ret i64 %r
none:
  ret i64 0
}

; CHECK-LABEL: @count(
; CHECK: %r = add nsw i64 %n.t.t, 0, !srange ![[R:[0-9]+]]
; CHECK: ![[R]] = !{!"n", !"n", !"1",
