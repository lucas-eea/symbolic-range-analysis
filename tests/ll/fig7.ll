; CHECK: === Symbolic Range Analysis: fig7 ===
; CHECK: %b.t = phi
; CHECK-NEXT: => [43, b]
; CHECK: %a.t = phi
; CHECK-NEXT: => [42, min((b - 1), 42)]
; CHECK: %c.t = phi
; CHECK-NEXT: => [44, (b + 1)]
; CHECK: %v.t =
; CHECK-NEXT: => [29, (b + 1)]

define i32 @fig7(i32 %b, i32 %x) {
entry:
  %a = add i32 0, 42
  %c = add i32 %b, 1
  %v = sub i32 %c, %x
  %cmp = icmp slt i32 %a, %b
  br i1 %cmp, label %true, label %false

true:
  ret i32 %v

false:
  ret i32 %v
}
