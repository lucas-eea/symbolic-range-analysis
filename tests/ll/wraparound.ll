; Checks for tests/c/wraparound.c.

; CHECK-LABEL: @hash_top_byte(
; CHECK-NOT: %mul = mul i32 {{.*}}!srange
; CHECK: %shr = lshr i32 %mul, 24, !srange ![[BYTE:[0-9]+]]
; CHECK-LABEL: @scaled(
; CHECK: %mul = mul nsw i32 %conv, 1000, !srange ![[SC:[0-9]+]]
; CHECK-DAG: ![[BYTE]] = !{!"0", !"255", !"0", !"255"}
; CHECK-DAG: ![[SC]] = !{!"1000*c", !"1000*c", !"-128000", !"127000"}
