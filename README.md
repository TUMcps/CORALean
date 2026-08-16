# CORALean 🪸

A Lean 4 formalization of [CORA](https://cora.in.tum.de), the Continuous
Reachability Analyzer.

Set representations and their operations are defined over ℝ and proved
sound — each operation over-approximates the set it claims to. Soundness is
stated once, as `⊆`, so the floating-point layer refines this one along the same
relation: a float zonotope denotes a set of real points just as an exact one
does, so it needs no second notion of correctness, and the two compose by
transitivity.

The floating-point layer assumes no format. `SoundFloatArithmetic F` asks only
for a real interpretation and arithmetic that rounds in a stated direction, so
its proofs hold for binary64, for any other precision, and — as the instance
that keeps the class honest — for ℝ itself.

## Layout

Mirrors CORA's, and its names: `plus`, `mtimes`, `reduce`, `interval`.

```
lean/CORALean/
  Global/          shared: array types, index partitions, the ContSet
                   interface, the Mathlib surface
  Arithmetic/
    Real/          the specification: exact arithmetic over ℝ
      ContSet/     one directory per representation
        Interval/  API.lean (definitions), Theorems.lean (guarantees), Proofs/
        Zonotope/
    Float/         the refinement: the same representations, rounded
      SoundFloatArithmetic.lean   what the layer assumes of its scalar
      Instances/   Real (rounding trivial), Dyadic (rounding real)
```

Per representation, `API` defines, `Theorems` states one guarantee per
operation, and `Proofs/` holds one file per proof.

`Real` and `Float` are siblings on disk but not in the import graph. `Float`
imports `Real`, because a rounded operation is proved sound by composing the
exact guarantee with the direction the rounding went. Deleting `Float` leaves
`Real` standing; the reverse does not hold.

## Build

```
cd lean && lake exe cache get && lake build
```

Requires the toolchain in `lean/lean-toolchain`; `elan` installs it
automatically.

## Notes

Heuristics carry no proof obligation. `reduce` takes a partition of the
generator indices and is sound for *every* partition, so CORA's twenty-odd
generator-selection rules are one definition with different inputs.

Proofs are written explicitly rather than by search — `maxHeartbeats` is set to
5000, well under Lean's default, so a proof that starts searching fails loudly.
