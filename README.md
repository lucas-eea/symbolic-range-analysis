# Symbolic Range Analysis

Implementation of the symbolic range analysis described in:

> Nazaré et al. [*Validation of Memory Accesses Through Symbolic Analyses*](https://homepages.dcc.ufmg.br/~fernando/publications/papers/OOPSLA14.pdf), OOPSLA 2014.

## Prerequisites

- [LLVM](https://llvm.org/)
- [GiNaC](https://www.ginac.de/) — required for the symbolic range analysis pass

## Build
```bash
# If llvm-config is on your PATH, no extra configuration is needed.
# Otherwise, point LLVM_DIR at your installation's CMake configuration directory:
# export LLVM_DIR=/usr/lib/llvm-17/lib/cmake/llvm
scripts/build.sh
```

## Usage

### Step 0 - Compile C to LLVM IR
```bash
 clang -O0 -S -emit-llvm -fno-discard-value-names tests/test.c -o test.ll
```

### Step 1 — Convert to E-SSA form

Run `mem2reg` first to promote allocas to SSA registers, then apply the ESSAfier pass:

```bash
opt -load-pass-plugin=build/ESSAfier.so \
    -passes="mem2reg,ESSAfier" \
    -S tests/input.ll \
    -o tests/output.ll
```
#### Expected Results
The output file `tests/output.ll` is the E-SSA form of the input, which adds σ-nodes, i.e: copies of variables at conditionals with renamed variables (`.t`/`.f` suffixes) at branch targets.
Additionally, the pass also places copies of variables which  depend transitively on the variables at conditionals and that are used in a label dominated by the branch target.

For instance, see this C Program:
```c
// tests/c/transitive_dependences_handling.c
int test(int a, int b) {
    int x = a + 1;   // x transitively depends on a (directly)
    int y = x * 2;   // y transitively depends on a through x
    if (a < b) {
        int p = y + 1;
        return p;    // y is consumed here → copies of x and y appear in if.then
    }
    return 0;        // false branch never touches y → no copies for dependences there
}
```

After ESSAfier, the true branch becomes:

```llvm
if.then:
  %b.t   = phi i32 [ %b, %entry ], !sigma !...
  %a.t   = phi i32 [ %a, %entry ], !sigma !...
  %add.t = add nsw i32 %a.t, 1        ; copy of x = a+1, rewritten to use a.t
  %mul.t = mul nsw i32 %add.t, 2      ; copy of y = x*2, rewritten to use add.t
  %add1  = add nsw i32 %mul.t, 1      ; original p = y+1, rewritten to use mul.t
  br label %if.end
if.end:                                ; false branch: σ-nodes only, no copies
  %b.f = phi i32 [ %b, %entry ], !sigma !...
  %a.f = phi i32 [ %a, %entry ], !sigma !...
  br label %return
```

This is useful because we can be more precise about the ranges of the .t or .f copies.

### Step 2 — Run Symbolic Range Analysis

Feed the E-SSA IR into the range-analysis annotator pass. It annotates every instruction that has a non-trivial symbolic range with `!srange` metadata:

```bash
opt -load-pass-plugin=./build/ESSAfier.so \
    -load-pass-plugin=./build/SymbolicRanges.so \
    -passes="function(ESSAfier),sra-annotator" \
    -S input.ll -o annotated.ll
```
#### Expected Results
This Pass annotates instructions with `!srange !N` metadata, where `!N` is a two-operand `MDNode`:

```llvm
!N = !{!"<lower>", !"<upper>"}
```

Both operands are `MDString` values serialized by GiNaC in its canonical polynomial form — e.g. `b+1` is printed as `"1+b"`.

**Example** — `tests/c/symbolic_range_analysis_fig7.c` with `x ∈ [0, 15]`:

```c
int fig7(int b, int x) {
    int a = 42;
    int c = b + 1;          // range: [b+1, b+1]
    int v = c - x;          // range: [(b+1)−15, (b+1)−0] = [b−14, b+1]
    if (a < b) { return v; }
    return v;
}
```

```bash
clang -O0 -S -emit-llvm -Xclang -disable-O0-optnone \
    -fno-discard-value-names tests/c/symbolic_range_analysis_fig7.c -o - | \
opt -passes=mem2reg -S | \
opt -load-pass-plugin=./build/ESSAfier.so \
    -load-pass-plugin=./build/SymbolicRanges.so \
    -passes="function(ESSAfier),sra-annotator<x=0:15>" \
    -S -o annotated.ll
```

Relevant annotations in `annotated.ll`:

```llvm
%add = add nsw i32 %b, 1,       !srange !C
%sub = sub nsw i32 %add, %x,    !srange !V
...
!C = !{!"1+b",   !"1+b"}     ; encodes [b+1, b+1]
!V = !{!"-14+b", !"1+b"}     ; encodes [b−14, b+1]
```

The `sra-annotator` pass also accepts per-argument concrete ranges as `sra-annotator<arg=lo:hi,...>` — used above to supply `x ∈ [0, 15]`.

### Running both passes together

```bash
opt -load-pass-plugin=./build/ESSAfier.so \
    -load-pass-plugin=./build/SymbolicRanges.so \
    -passes="function(ESSAfier),sra-annotator" \
    -S input.ll -o annotated.ll
```

### Running Tests
You can run all tests using:
```bash
scripts/run_tests.sh
```

This compiles each test in `tests/c/`, runs ESSAfier and/or SRA, and checks the output against the LLVM `FileCheck` patterns in `tests/ll/`.
It also runs the `SymBoxes` lattice tests for the semi-lattice operations: join, widening, and symbolic equality.
