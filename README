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

Also, the binaries for tests/
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

### Running both passes together

You need two `opt` invocations for that:

```bash
opt -load-pass-plugin=build/ESSAfier.so \
    --passes="mem2reg,ESSAfier" \
    -S tests/input.ll \
    -o tests/essa.ll

opt -load-pass-plugin=build/SymbolicRanges.so \
    --passes="sra-annotator" \
    --disable-output \
    tests/essa.ll
```

### Running the unit tests

This runs the `SymBoxes` lattice tests for the semi-lattice operations: join, widening, and symbolic equality.

```bash
build/symboxes
```
