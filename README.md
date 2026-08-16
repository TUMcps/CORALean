# CORALean 🪸

A Lean 4 formalization of [CORA](https://cora.in.tum.de), the Continuous
Reachability Analyzer.

## Build

```
cd lean && lake exe cache get && lake build
```

Requires the toolchain in `lean/lean-toolchain`; `elan` installs it
automatically.


## Layout

Two halves. `lean/` holds the definitions and their proofs; `targets/` holds
one directory per languages implementing actual code.

```
lean/
  src/           the formalization — definitions, theorems, proofs
targets/
  c/             Lean's own compiler output, copied out of .lake  (generated)
    src/                 the exported C, mirroring the Lean modules
    export-from-lake.sh  clean rebuild, then copy
  cpp/           written by hand against the Lean sources         (transcribed)
```

The C code is generated from lean and serves as the reference.
Every other languange should be generated or at least checked against the C implementation. 

### The formalization

Mirrors CORA's structure and naming convention.

Set representations and their operations are defined over ℝ and proved
sound — e.g., each operation over-approximates the set it claims to. 

Lean also fromalizes the floating point computations so it can be implemented in actual code (see generated c code).
Thus, all theorems are first stated in ℝ under `lean/src/CORALean/Arithmetic/Real` and then refined in `.../Float`.
The floating-point layer assumes no format. `SoundFloatArithmetic F` asks only
for a real interpretation and arithmetic that rounds in a stated direction, so
its proofs hold for binary64, for any other precision.
The proofs of `Float` then just refines the theorems in `Real`, which gives soundness by transitivity.


```
lean/src/CORALean/
  Global/          shared: array types, index partitions, the Mathlib surface
  Arithmetic/
    Real/          the specification: exact arithmetic over ℝ
      ContSet/     one directory per concept
        ContSet/   the interface every representation instantiates
        Interval/  API.lean (definitions), Theorems.lean (guarantees), Proofs/
        ...
    Float/         the refinement: the same representations, rounded
      FloatOps / SoundFloatArithmetic   operations, then their guarantees
      Instances/   Real (rounding trivial), Dyadic (rounding real)
      ContSet/
        InflatedContSet/   nominal part + error box, and its shared lemmas
        Interval/  Floating point formalization of Interval in Real
        ...
```


## Contributing

See [CONTRIBUTING.md](CONTRIBUTING.md) for file roles, the layering rule, and
the conventions proofs and docstrings follow.
