; Reduced from Polybench seidel-2d. The false target is the branching block
; itself (a self loop): copies placed at its top used values defined later.

define i32 @main() {
bb:
  br label %bb58

bb58:                                             ; preds = %bb58, %bb
  %i67 = add i64 0, 0
  %i66 = fadd double 0.000000e+00, 0.000000e+00
  %i68 = getelementptr double, ptr null, i64 %i67
  %i69 = load double, ptr %i68, align 8
  %i70 = fadd double %i66, %i69
  %i71 = fadd double 0.000000e+00, %i70
  %i83 = icmp eq i64 %i67, 0
  br i1 %i83, label %bb84, label %bb58

bb84:                                             ; preds = %bb58
  ret i32 0
}

; CHECK-NOT: .f =
; CHECK-LABEL: bb84:
; CHECK-NEXT: %i67.t = phi i64 [ %i67, %bb58 ], !sigma
