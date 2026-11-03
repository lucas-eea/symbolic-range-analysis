; Reduced from gcc-torture 20011126-2. The false target %bb43 has two
; predecessors, so nothing may be placed there; the compared phi %i51 must
; never be cloned.

define ptr @main() {
bb:
  br label %bb13

bb13:                                             ; preds = %bb
  br i1 false, label %bb49, label %bb27

bb27:                                             ; preds = %bb13
  br label %bb43

bb43:                                             ; preds = %bb49, %bb27
  %i44 = phi ptr [ null, %bb27 ], [ %i52, %bb49 ]
  ret ptr %i44

bb49:                                             ; preds = %bb49, %bb13
  %i51 = phi ptr [ null, %bb49 ], [ null, %bb13 ]
  %i52 = getelementptr i8, ptr %i51, i64 1
  %i55 = icmp ult ptr %i51, null
  br i1 %i55, label %bb49, label %bb43
}

; CHECK-NOT: %i51.
; CHECK-NOT: !sigma
