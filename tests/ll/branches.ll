; RUN: opt -load-pass-plugin=%plugin_essafier -passes=ESSAfier \
; RUN:   -load-pass-plugin=%plugin_sra -passes=sra-annotator \
; RUN:   -disable-output %s 2>&1 | FileCheck %s

define i32 @slt_branch(i32 %a, i32 %b) {
entry:
  %cmp = icmp slt i32 %a, %b
  br i1 %cmp, label %true, label %false
true:
  ret i32 %a
false:
  ret i32 %a
}

; CHECK: === Symbolic Range Analysis: slt_branch ===
; CHECK: %b.t = phi
; CHECK-NEXT: => [max((a + 1), b), b]
; CHECK: %a.t = phi
; CHECK-NEXT: => [a, min((b - 1), a)]
; CHECK: %b.f = phi
; CHECK-NEXT: => [b, min(a, b)]
; CHECK: %a.f = phi
; CHECK-NEXT: => [max(a, b), a]
