# cpp — written by hand against the Lean sources

`src/` is a header-only C++20 transcription of the float layer in `lean/`.
It is written rather than generated from Lean, so nothing enforces the
correspondence to the Lean sources — it is maintained by hand.

## Building

Header-only; compile against `src/`.

```bash
g++ -std=c++20 -Wall -Wextra -Werror -frounding-math -ffp-contract=off -O2 \
    -Isrc -o zonotope tests/zonotope.cpp && ./zonotope
```

## Tests

`./tests/run.sh` builds and runs everything. One suite per concern, sharing the
harness in `check.hpp` — no framework, so a test reads next to the Lean theorem
it stands for.

| suite | what it checks |
| --- | --- |
| `examples.cpp` | worked cases with hand-computed answers |
| `float_ops.cpp` | the `SoundFloatArithmetic` axioms, over random doubles |
| `interval.cpp` | each operation encloses what it claims to |
| `zonotope.cpp` | the `_outer` theorems, and the key lemma of each proof |

Two patterns worth reusing:

**Exactly representable data.** The enclosure suites draw integer centres and
generators and coefficients that are multiples of 1/1024, so the reference point
is computed without rounding and every check is an equality or a strict bound —
no tolerances anywhere. Rounding is exercised in `float_ops.cpp`, where it is
the subject rather than a nuisance.

**Check the proof's lemma, not just the conclusion.** Deciding membership in a
zonotope means solving for coefficients, so the sampled-point tests settle for
the interval hull, which is necessary but not sufficient. The proofs, though,
all turn on a step of the form "this radius covers what that part can
contribute" — a comparison of two numbers. `zonotope.cpp` reads those radii off
the block the operation actually produced and checks them directly, which is
exact and as strong as the proof step it mirrors.

The suites were checked against mutants rather than assumed to work: flipping
`addDown` to round up fails 305 checks in `float_ops`, pointing `reduce` at the
kept generators instead of the dropped ones fails 783 in `zonotope`, and
dropping the sign handling from `Interval::mtimes` fails 388 in `interval`.

*TODO:* compare against the `../c` implementation (and ideally even verify!)


## Correspondence

Each header names its specification in its first lines; paths below are relative
to `lean/src/CORALean/`.

| header           | specification                                             |
| ---------------- | --------------------------------------------------------- |
| `tensor.hpp`     | `Global/Tensor.lean`                                       |
| `partition.hpp`  | `Global/Partition.lean`                                    |
| `float_ops.hpp`  | `Float/FloatOps.lean`                                      |
| `binary64.hpp`   | no counterpart — see *Assumptions*                         |
| `interval.hpp`   | `Float/ContSet/Interval/Operations/`                       |
| `zonotope.hpp`   | `Float/ContSet/Zonotope/Operations/`                       |

Names follow CORA and Lean exactly — `plus`, `mtimes`, `reduce`,
`reduceAndAbsorb`, `absorbError`, `interval` — so a definition can be compared
against its specification line by line. That is the only thing keeping the two
in step, so it is worth more here than C++ house style.

`FloatOps<F>` is the Lean class as a traits struct, and every algorithm is a
template over it, exactly as the Lean definitions are generic in `F`.

## What is not here, and why

**`Real/` and `SoundFloatArithmetic`.** Denotations and proofs do not
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
