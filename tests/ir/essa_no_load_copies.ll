; Instructions that read memory are never copied to a branch target: the copy
; could observe a different value than the original. Pure dependents are
; copied, keeping their memory operands (here %l) unchanged.

define i32 @f(ptr %p, i32 %a, i32 %b) {
entry:
  %x = add i32 %a, 1
  %g = getelementptr i32, ptr %p, i32 %a
  %l = load i32, ptr %g
  %y = add i32 %l, %x
  %c = icmp slt i32 %a, %b
  br i1 %c, label %then, label %else
then:
  %r = add i32 %y, %x
  ret i32 %r
else:
  ret i32 0
}

; CHECK-LABEL: then:
; CHECK: %x.t = add i32 %a.t, 1
; CHECK-NEXT: %y.t = add i32 %l, %x.t
; CHECK-NOT: load
; CHECK-LABEL: else:
