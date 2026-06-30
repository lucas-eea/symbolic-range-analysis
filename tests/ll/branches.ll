; Generated from tests/c/branches.c

; CHECK-LABEL: @slt_branch
; CHECK: if.then:
; CHECK-NEXT: %b.t = phi i32 [ %b, %entry ], !sigma ![[ST:[0-9]+]]
; CHECK-NEXT: %a.t = phi i32 [ %a, %entry ], !sigma ![[ST]]
; CHECK-NEXT: br label %return
; CHECK: if.end:
; CHECK-NEXT: %b.f = phi i32 [ %b, %entry ], !sigma ![[SF:[0-9]+]]
; CHECK-NEXT: %a.f = phi i32 [ %a, %entry ], !sigma ![[SF]]
; CHECK-NEXT: br label %return
; CHECK: ![[ST]] = !{!".t"}
; CHECK: ![[SF]] = !{!".f"}
