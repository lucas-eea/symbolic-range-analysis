; Checks for tests/c/exact_values.c: exact values decide the equalities
; (false) after the loops, but not when the comparison may go either way.

; CHECK-LABEL: @two_loops(
; CHECK: icmp ne i32 %mul4, %j.1, {{.*}}!srange.cmp ![[F:[0-9]+]]
; CHECK-LABEL: @two_params(
; CHECK: icmp ne i32 %mul, %j.1, {{.*}}!srange.cmp ![[F]]
; CHECK-LABEL: @irregular(
; CHECK: icmp ne i32 %mul, %j.0, {{.*}}!srange.cmp ![[F]]
; CHECK-LABEL: @wrapping(
; CHECK-NOT: !srange.cmp
; CHECK-LABEL: @equal_trips(
; CHECK: icmp ne i32 %j.0, %k.0, {{.*}}!srange.cmp ![[F]]
; CHECK-LABEL: @unequal_trips(
; CHECK-NOT: !srange.cmp
; CHECK-LABEL: @stride2(
; CHECK-NOT: icmp ne i32 %i.0.f, %n.f, {{.*}}!srange.cmp
; CHECK-LABEL: }
; CHECK: ![[F]] = !{!"false"}
