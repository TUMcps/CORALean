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
  Global/          shared: array types, index partitions, the Mathlib surface
  Arithmetic/
    Real/          the specification: exact arithmetic over ℝ
      ContSet/     one directory per concept
        ContSet/   the interface every representation instantiates
        Interval/  API.lean (definitions), Theorems.lean (guarantees), Proofs/
        Zonotope/
    Float/         the refinement: the same representations, rounded
      FloatOps / SoundFloatArithmetic   operations, then their guarantees
      Instances/   Real (rounding trivial), Dyadic (rounding real)
      ContSet/
        Interval/
        Zonotope/
        InflatedContSet/   nominal part + error box, and its shared lemmas
```

Per representation, `API` defines, `Theorems` states one guarantee per
operation, and `Proofs/` holds one file per proof.

`Real` and `Float` are siblings on disk but not in the import graph. `Float`
imports `Real`, and a float representation does not define what it denotes: its
`construct` *is* the exact one, applied to the bounds read through `toReal`.

`ContSet` lives in `Real` rather than somewhere neutral because the set a
representation denotes is always over ℝ. `Float` instantiates it as
`Real.ContSet`, which says what a floating-point representation is: something
denoting a real continuous set.

So a float operation never proves soundness directly. It proves only that it
encloses the exact operation — `plus_refines`, `mtimes_refines` — and soundness
follows by transitivity. Set-level reasoning (Minkowski sums, images under a
linear map, the sign of a coefficient) is written once, in `Real`, and never
repeated. Deleting `Float` leaves `Real` standing; the reverse does not hold.

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

## Contributing

See [CONTRIBUTING.md](CONTRIBUTING.md) for file roles, the layering rule, and
the conventions proofs and docstrings follow.
