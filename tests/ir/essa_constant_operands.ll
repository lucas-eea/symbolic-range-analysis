; Reduced from testcase-InstCombine-1. Constants are never renamed: no sigma
; nodes are created for `icmp eq i32 0, 0`, and uses of 0 are left alone.

define i32 @main() {
bb:
  %i1 = icmp eq i32 0, 0
  br i1 %i1, label %common.ret, label %bb2

bb2:                                              ; preds = %bb
  %i4 = and i32 0, 0
  %i5 = icmp eq i32 0, 0
  br i1 %i5, label %common.ret, label %bb6

bb6:                                              ; preds = %bb6, %bb2
  %i11 = icmp eq i32 0, %i4
  br label %bb6

common.ret:                                       ; preds = %bb2, %bb
  ret i32 0
}

; CHECK-NOT: !sigma
; CHECK: %i4 = and i32 0, 0
