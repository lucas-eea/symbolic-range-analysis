; A counter stepping by 4 under i < 16 is at most 12 in the loop body, so
; i + 3 is at most 15. Under a symbolic bound n the body maximum is
; 4 * ((n - 1) / 4). With step 3 the body sees 15 and i + 3 reaches 18.

define void @by4() {
entry:
  br label %head
head:
  %i = phi i32 [ 0, %entry ], [ %next, %body ]
  %go = icmp slt i32 %i, 16
  br i1 %go, label %body, label %exit
body:
  %idx = add nsw i32 %i, 3
  %next = add nsw i32 %i, 4
  br label %head
exit:
  ret void
}

define void @by4_sym(i32 %n) {
entry:
  br label %head
head:
  %i = phi i32 [ 0, %entry ], [ %next, %body ]
  %go = icmp slt i32 %i, %n
  br i1 %go, label %body, label %exit
body:
  %idx = add nsw i32 %i, 3
  %next = add nsw i32 %i, 4
  br label %head
exit:
  ret void
}

; for (x = b; x < b + 8; x += 4), with the bound recomputed in the header as
; -O0 code does: the body sees x <= b + 4 whatever b is, so x + 3 <= b + 7.
define void @by4_rel(i32 %b) {
entry:
  br label %head
head:
  %x = phi i32 [ %b, %entry ], [ %next, %body ]
  %end = add nsw i32 %b, 8
  %go = icmp slt i32 %x, %end
  br i1 %go, label %body, label %exit
body:
  %idx = add nsw i32 %x, 3
  %next = add nsw i32 %x, 4
  br label %head
exit:
  ret void
}

; CHECK-LABEL: @by4(
; CHECK: %idx = add nsw i32 %i.t, 3, !srange ![[B4:[0-9]+]]
; CHECK-LABEL: @by4_sym(
; CHECK: %idx = add nsw i32 %i.t, 3, !srange ![[BS:[0-9]+]]
; CHECK-LABEL: @by4_rel(
; CHECK: %idx = add nsw i32 %x.t, 3, !srange ![[BR:[0-9]+]]
; CHECK-DAG: ![[B4]] = !{!"3", !"15", !"3", !"15"}
; CHECK-DAG: ![[BS]] = !{!"3", !"min(2+n, 3+4*idiv(-1+n,4))",
; CHECK-DAG: ![[BR]] = !{!"3+b", !"7+b",
