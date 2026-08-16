# cpp — written by hand against the Lean sources

`src/` is a header-only C++20 transcription of the float layer in `lean/`. It is
written, not generated: the Lean sources are its specification, and the
correspondence is maintained by hand.

This is the code meant to run. [`../c`](../c) is the same algorithms as Lean
itself compiles them — correct but boxed and closure-heavy — and serves as the
reference to check this against.

## Correspondence

Each header names its specification in its first lines.

| header           | specification                                             |
| ---------------- | --------------------------------------------------------- |
| `tensor.hpp`     | `Global/Tensor.lean`                                       |
| `partition.hpp`  | `Global/Partition.lean`                                    |
| `float_ops.hpp`  | `Arithmetic/Float/FloatOps.lean`                           |
| `binary64.hpp`   | no counterpart — see *Assumptions*                         |
| `interval.hpp`   | `Arithmetic/Float/ContSet/Interval/API.lean`               |
| `zonotope.hpp`   | `Arithmetic/Float/ContSet/Zonotope/API.lean`               |

Names follow CORA and Lean exactly — `plus`, `mtimes`, `reduce`,
`reduceAndAbsorb`, `absorbError`, `interval` — so a definition can be compared
against its specification line by line. That is the only thing keeping the two
in step, so it is worth more here than C++ house style.

`FloatOps<F>` is the Lean class as a traits struct, and every algorithm is a
template over it, exactly as the Lean definitions are generic in `F`.

## What is not here, and why

**`Arithmetic/Real/` and `SoundFloatArithmetic`.** Denotations and proofs do not
run. That the float layer erases to something executable is the point of the
split, and this directory is what is left after the erasure.

**`InflatedContSet`.** `nominal` and `construct` are denotations. What survives
is the field `E` and the discipline of paying every rounding into it.

**Dimensions in types.** Lean writes `Zonotope F n h`; `h` changes with every
operation, so C++ would need them at compile time. They are fields here, checked
by `assert`. This is the one place the C++ type system is weaker than Lean's.

**`Split` as a bijection.** Only `left` and `right` are ever computed with, so it
is two index vectors. Lean gets "names every index exactly once" from the
equivalence; here `isValid` checks it at run time, and `reduce` asserts it —
overlapping or missing indices would silently drop a generator.

## Rounding

The mode is set once to `FE_UPWARD` by `RoundUpGuard` and never changed;
switching per operation would dominate the run time. The downward operations
negate into the upward one, which is exact:

```cpp
static double addDown(double a, double b) { return -((-a) + (-b)); }
```

Every call into the library must be inside a `RoundUpGuard`. Under any other
mode the results are wrong, not merely imprecise.

`sumUp` is right-nested, matching the Lean recursion. `addUp` is not
associative, so the bracketing is part of the definition — folding the other way
computes a different float and breaks agreement with `../c`.

## Assumptions

`binary64.hpp` has no Lean counterpart, and cannot: instantiating `F` at
binary64 is an assumption about this file and the toolchain rather than a
theorem. It requires:

- **no overflow, underflow, or NaN.** `Dyadic` has an unbounded exponent, which
  is exactly this assumption. binary64 has both ends: `half` is inexact on
  subnormals, and `addUp` saturating to `+∞` breaks the bound it is supposed to
  give. Carried as a written assumption, not checked.
- **compiler flags**, each of which independently breaks the `FloatOps` axioms
  if wrong: `-frounding-math` (the optimizer may otherwise fold constants under
  the wrong mode), `-ffp-contract=off` (an FMA rounds once, not twice), no
  `-ffast-math`, and SSE rather than x87 excess precision.

## Building

Header-only; compile against `src/`.

```bash
g++ -std=c++20 -Wall -Wextra -Werror -frounding-math -ffp-contract=off -O2 \
    -Isrc -o smoke tests/smoke.cpp && ./smoke
```

`tests/smoke.cpp` checks that directed rounding reaches the hardware and that
each operation keeps the generator count and the enclosure its Lean counterpart
promises. It does not compare against `../c`; that differential harness is the
next step, and until it exists the tie between this code and the theorems rests
on the transcription being read carefully.
