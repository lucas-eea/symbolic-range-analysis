; Checks for tests/c/transitive_dependences_handling.c: x = a+1 and y = x*2
; are recomputed in the true branch from the sigma of a, and p uses the copy.
; The false branch never uses y, so it only gets sigma nodes.

; CHECK-LABEL: if.then:
; CHECK-DAG: %b.t = phi i32 [ %b, %entry ], !sigma
; CHECK-DAG: %a.t = phi i32 [ %a, %entry ], !sigma
; CHECK: %add.t = add nsw i32 %a.t, 1
; CHECK-NEXT: %mul.t = mul nsw i32 %add.t, 2
; CHECK-NEXT: %add1 = add nsw i32 %mul.t, 1
; CHECK-LABEL: if.end:
; CHECK-DAG: %b.f = phi i32 [ %b, %entry ], !sigma
; CHECK-DAG: %a.f = phi i32 [ %a, %entry ], !sigma
; CHECK-NOT: .f = add
; CHECK-LABEL: return:
