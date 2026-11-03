# Symbolic Range Analysis

LLVM pass plugins that implement the symbolic range analysis described in:

> Nazaré et al. [*Validation of Memory Accesses Through Symbolic Analyses*](https://homepages.dcc.ufmg.br/~fernando/publications/papers/OOPSLA14.pdf), OOPSLA 2014.

with an optional pass that rewrites the code based on its results.

## Prerequisites

- [LLVM](https://llvm.org/)
- [GiNaC](https://www.ginac.de/) — required for the symbolic range analysis pass

## Build

```bash
scripts/build.sh
```

This builds `ESSAfier.so`, `SymbolicRanges.so` and `SRACVP.so` in `build/`.
If `llvm-config` is not on your `PATH`, set `LLVM_DIR` to LLVM's CMake
directory first, for example `export LLVM_DIR=/usr/lib/llvm-22/lib/cmake/llvm`.

## Usage

### Step 0: compile C to LLVM IR

```bash
clang -O0 -Xclang -disable-O0-optnone -fno-discard-value-names \
    -emit-llvm -S test.c -o test.ll
```

`-disable-O0-optnone` lets `opt` optimize the functions, and
`-fno-discard-value-names` keeps the names of the C variables.

### Step 1: e-SSA form (ESSAfier)

```bash
opt -load-pass-plugin=build/ESSAfier.so \
    -passes='function(mem2reg),function(ESSAfier)' test.ll -S -o essa.ll
```

At each branch on a comparison, ESSAfier gives the compared values a new name
on each side: a phi with one incoming value, tagged `!sigma`. For

```c
int f(int a, int b) {
  if (a < b)
    return b - a;
  return 0;
}
```

the output is

```llvm
if.then:                                ; a < b holds here
  %b.t = phi i32 [ %b, %entry ], !sigma !4
  %a.t = phi i32 [ %a, %entry ], !sigma !4
  %sub = sub nsw i32 %b.t, %a.t
  br label %return

if.end:                                 ; a >= b holds here
  %b.f = phi i32 [ %b, %entry ], !sigma !5
  %a.f = phi i32 [ %a, %entry ], !sigma !5
  br label %return
```

`%a.t` is `a` where `a < b` is known, so it can get a tighter range than `a`.

### Step 2: symbolic ranges (sra-annotator)

```bash
opt -load-pass-plugin=build/ESSAfier.so \
    -load-pass-plugin=build/SymbolicRanges.so \
    -passes='function(mem2reg),function(ESSAfier),sra-annotator' \
    test.ll -S -o sra.ll
```

`sra-annotator` tags every integer with `!srange !{lower, upper, numeric lower,
numeric upper}`. The bounds are expressions over the function's unknowns
(arguments, loads, calls). For the same function:

```llvm
%a.t = phi i32 [ %a, %entry ], !sigma !8, !srange !10
%sub = sub nsw i32 %b.t, %a.t, !srange !11

!10 = !{!"a", !"min(-1+b, a)", !"-2147483648", !"2147483646"}   ; a <= b - 1
!11 = !{!"max(-a+b, 1, 2-b+a)", !"-a+b", !"1", !"2147483647"}  ; b - a >= 1
```

Comparisons whose result the ranges decide get `!srange.cmp = "true"` or
`"false"`.

### Step 3: rewriting the code (sra-cvp)

```bash
opt -load-pass-plugin=build/SRACVP.so \
    -passes='function(mem2reg),sra-cvp,function(simplifycfg)' \
    test.ll -S -o opt.ll
```

`sra-cvp` runs ESSAfier and sra-annotator on a copy of the module, replaces
the comparisons they decide with `true` or `false`, and adds the `nsw` and
`nuw` flags they prove. `simplifycfg` then deletes the blocks that can no
longer run. For `tests/c/test08.c`:

```c
void foo(const int M, const int N, const int P) {
    if (P > N) {
        if (N > M) {
            if (M > P) {
                printf("Dumb as a post\n");
            }
        }
    }
}
```

inside both `if`s the analysis finds `M <= P - 2`, so `M > P` is always false,
and the printf is removed:

```llvm
define dso_local void @foo(i32 noundef %M, i32 noundef %N, i32 noundef %P) {
entry:
  %cmp = icmp sgt i32 %P, %N
  br i1 %cmp, label %if.then, label %if.end6

if.then:
  %cmp1 = icmp sgt i32 %N, %M
  br label %if.end6

if.end6:
  ret void
}
```

`sra-cvp` prints what it changed on stderr:

```
sra-cvp: {"cmp_true": 0, "cmp_false": 1, "nsw": 0, "nuw": 0, ...}
```

Other rewrites are off by default: `-sra-cvp-signs`, `-sra-cvp-more`,
`-sra-cvp-overflow`, `-sra-cvp-alias` and `-sra-cvp-facts`. Run
`opt -load-pass-plugin=build/SRACVP.so --help-hidden` for the full list.

## Tests

```bash
scripts/run_tests.sh
```

The script checks the output of the passes on the programs in `tests/` with
`FileCheck`, including the removal of the printfs in `tests/c/test05.c` and
`tests/c/test08.c`.
