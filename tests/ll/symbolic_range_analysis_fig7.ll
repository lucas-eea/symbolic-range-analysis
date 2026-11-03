; Checks for tests/c/symbolic_range_analysis_fig7.c with x in [0, 15]
; (fig. 7 of Nazaré et al.): c = b + 1 is [b+1, b+1], v = c - x is [b-14, b+1].
; The last two operands are the numeric hull, b bounded by its type (i32).

; CHECK: %add = add nsw i32 %b, 1, !srange ![[C:[0-9]+]]
; CHECK: %sub = sub nsw i32 %add, %x, !srange ![[V:[0-9]+]]
; CHECK-DAG: ![[C]] = !{!"1+b", !"1+b", !"-2147483647", !"2147483647"}
; CHECK-DAG: ![[V]] = !{!"-14+b", !"1+b", !"-2147483648", !"2147483647"}
