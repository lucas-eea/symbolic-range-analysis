; Checks for tests/c/casts_and_bits.c: casts, comparisons, bitwise operations
; and symbols bounded by their types.

; CHECK-LABEL: @zext_char(
; CHECK: %conv = zext i8 %c to i32, !srange ![[BYTE:[0-9]+]]
; CHECK-LABEL: @sext_char_plus1(
; CHECK: %conv = sext i8 %c to i32, !srange ![[SC:[0-9]+]]
; CHECK: %add = add nsw i32 %conv, 1, !srange ![[SC1:[0-9]+]]
; CHECK-LABEL: @low_bits(
; CHECK: %and = and i32 %x, 15, !srange ![[NIBBLE:[0-9]+]]
; CHECK-LABEL: @shift_right(
; CHECK: %shr = lshr i32 %x, 28, !srange ![[NIBBLE]]
; CHECK-LABEL: @is_less(
; CHECK: %cmp = icmp slt i32 %a, %b, !srange ![[BOOL:[0-9]+]]
; CHECK: %conv = zext i1 %cmp to i32, !srange ![[ZBOOL:[0-9]+]]
; CHECK-LABEL: @trunc_small(
; CHECK: %conv = trunc i32 %and to i16, !srange ![[BYTE]]
; CHECK-LABEL: @pick(
; CHECK: %cond = phi i32 {{.*}}, !srange ![[PICK:[0-9]+]]
; CHECK-DAG: ![[BYTE]] = !{!"0", !"255", !"0", !"255"}
; CHECK-DAG: ![[SC]] = !{!"c", !"c", !"-128", !"127"}
; CHECK-DAG: ![[SC1]] = !{!"1+c", !"1+c", !"-127", !"128"}
; CHECK-DAG: ![[NIBBLE]] = !{!"0", !"15", !"0", !"15"}
; CHECK-DAG: ![[BOOL]] = !{!"-1", !"0", !"-1", !"0"}
; CHECK-DAG: ![[ZBOOL]] = !{!"0", !"1", !"0", !"1"}
; CHECK-DAG: ![[PICK]] = !{!"min(7, a)", !"max(7, a)",
