# Symbolic Range Analysis

Implementation of the symbolic range analysis described in:

> Nazaré et al. [*Validation of Memory Accesses Through Symbolic Analyses*](https://homepages.dcc.ufmg.br/~fernando/publications/papers/OOPSLA14.pdf), OOPSLA 2014.

## Build

```bash
mkdir build && cd build
cmake -G Ninja ..
ninja
```

This yields two LLVM pass plugins inside `build/`:
- `ESSAfier.so` — converts LLVM IR to Extended SSA form (E-SSA), plus inserts σ-nodes at branch targets.
- `SymbolicRanges.so` — runs the symbolic range analysis on E-SSA form IR.

## Usage

### Step 0 - Compile C to LLVM IR
```bash
 clang -O0 -S -emit-llvm -fno-discard-value-names tests/test.c -o test.ll
```

### Step 1 — Convert to E-SSA form

Run `mem2reg` first to promote allocas to SSA registers, then apply the ESSAfier pass to insert σ-nodes:

```bash
opt -load-pass-plugin=build/ESSAfier.so \
    -passes="mem2reg,ESSAfier" \
    -S tests/input.ll \
    -o tests/output.ll
```

The output file `tests/output.ll` is the E-SSA form of the input, with renamed variables (`.t`/`.f` suffixes) at branch targets.
#### Expected Results
##### Input
```llvm
define dso_local i32 @src(i32 noundef %a, i32 noundef %b) #0 {
entry:
  %add = add nsw i32 %b, 1
  %sub = sub nsw i32 %add, 8
  %cmp = icmp slt i32 %a, %b
  br i1 %cmp, label %if.then, label %if.else

if.then:                                          ; preds = %entry
  %add1 = add nsw i32 10, %a
  br label %if.end

if.else:                                          ; preds = %entry
  %add2 = add nsw i32 -10, %sub
  br label %if.end

if.end:                                           ; preds = %if.else, %if.then
  %p.0 = phi i32 [ %add1, %if.then ], [ %add2, %if.else ]
  %add3 = add nsw i32 %p.0, 100
  ret i32 %add3
}
```
##### Output
```llvm
define dso_local i32 @tgt(i32 noundef %a, i32 noundef %b) #0 {
entry:
  %add = add nsw i32 %b, 1
  %sub = sub nsw i32 %add, 8
  %cmp = icmp slt i32 %a, %b
  br i1 %cmp, label %if.then, label %if.else

if.then:                                          ; preds = %entry
  %b.t = phi i32 [ %b, %entry ]
  %a.t = phi i32 [ %a, %entry ]
  %add1 = add nsw i32 10, %a.t
  br label %if.end

if.else:                                          ; preds = %entry
  %b.f = phi i32 [ %b, %entry ]
  %a.f = phi i32 [ %a, %entry ]
  %add.f = add nsw i32 %b.f, 1
  %sub.f = sub nsw i32 %add.f, 8
  %add2 = add nsw i32 -10, %sub.f
  br label %if.end

if.end:                                           ; preds = %if.else, %if.then
  %p.0 = phi i32 [ %add1, %if.then ], [ %add2, %if.else ]
  %add3 = add nsw i32 %p.0, 100
  ret i32 %add3
}
```

**(WIP)**
### Step 2 — Run Symbolic Range Analysis

Feed the E-SSA IR into the range analysis pass:

```bash
opt -load-pass-plugin=build/SymbolicRanges.so \
    -passes="sra-annotator" \
    -disable-output \
    tests/output.ll
```

The pass prints each variable's symbolic range to stderr in the form `[lower, upper]`.

#### Expected Results
For the same input as step one, this output is expected:
```
entry:
    %add = add nsw i32 %b, 1
    => [(b + 1), (b + 1)]
    %sub = sub nsw i32 %add, 8
    => [((b + 1) - 8), ((b + 1) - 8)]
    %cmp = icmp slt i32 %a, %b
    => [-∞, +∞]
    br i1 %cmp, label %if.then, label %if.else
    => [-∞, +∞]
if.then:
    %b.t = phi i32 [ %b, %entry ], !sigma !3
    => [max((a + 1), b), b]
    %a.t = phi i32 [ %a, %entry ], !sigma !3
    => [a, min((b - 1), a)]
    %add1 = add nsw i32 10, %a.t
    => [(10 + a), (10 + min((b - 1), a))]
    br label %if.end
    => [-∞, +∞]
if.else:
    %b.f = phi i32 [ %b, %entry ], !sigma !4
    => [b, min(a, b)]
    %a.f = phi i32 [ %a, %entry ], !sigma !4
    => [max(a, b), a]
    %add.f = add nsw i32 %b.f, 1
    => [(b + 1), (min(a, b) + 1)]
    %sub.f = sub nsw i32 %add.f, 8
    => [((b + 1) - 8), ((min(a, b) + 1) - 8)]
    %add2 = add nsw i32 -10, %sub.f
    => [(-10 + ((b + 1) - 8)), (-10 + ((min(a, b) + 1) - 8))]
    br label %if.end
    => [-∞, +∞]
if.end:
    %p.0 = phi i32 [ %add1, %if.then ], [ %add2, %if.else ]
    => [min((10 + a), (-10 + ((b + 1) - 8))), max((10 + min((b - 1), a)), (-10 + ((min(a, b) + 1) - 8)))]
    %add3 = add nsw i32 %p.0, 100
    => [(min((10 + a), (-10 + ((b + 1) - 8))) + 100), (max((10 + min((b - 1), a)), (-10 + ((min(a, b) + 1) - 8))) + 100)]
    ret i32 %add3
    => [-∞, +∞]

```
### Running both passes together

```bash
opt -load-pass-plugin=./build/ESSAfier.so     -load-pass-plugin=./build/SymbolicRanges.so     -passes="function(ESSAfier),sra-annotator"     -disable-output tests/beforeESSAfier.ll:w
```

### Running the unit tests

This runs the `SymBoxes` lattice tests for the semi-lattice operations: join, widening, and symbolic equality.

```bash
build/symboxes
```
