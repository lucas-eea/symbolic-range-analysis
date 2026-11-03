; Reduced from gcc-torture pr43560. The true target is the loop header %bb4,
; which has two predecessors: the compared phi %i5 must not be cloned there.

define void @test() {
bb:
  %i2 = load i32, ptr null, align 4
  br label %bb4

bb4:                                              ; preds = %bb11, %bb
  %i5 = phi i32 [ %i12, %bb11 ], [ %i2, %bb ]
  br label %bb11

bb11:                                             ; preds = %bb4
  %i12 = or i32 %i5, 0
  %i15 = icmp sgt i32 %i5, 0
  br i1 %i15, label %bb4, label %bb16

bb16:                                             ; preds = %bb11
  ret void
}

; CHECK-NOT: %i5.t
; CHECK-LABEL: bb16:
; CHECK-NEXT: %i5.f = phi i32 [ %i5, %bb11 ], !sigma
