# CORALean

A Lean 4 formalization of [CORA](https://cora.in.tum.de), the Continuous
Reachability Analyzer.

Set representations and their operations are defined over ℝ and proved
sound — each operation over-approximates the set it claims to. Soundness is
stated once, as `⊆`, so that a later floating-point layer can refine this one
along the same relation.

## Layout

Mirrors CORA's, and its names: `plus`, `mtimes`, `reduce`, `interval`.

```
lean/CORALean/
  Global/        ambient types, index partitions, the Mathlib surface
  ContSet/       one directory per representation
    Interval/    API.lean (definitions), Theorems.lean (guarantees), Proofs/
    Zonotope/
```

Per representation, `API` defines, `Theorems` states one guarantee per
operation, and `Proofs/` holds one file per proof.

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
