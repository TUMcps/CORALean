# CORALean 🪸

A Lean 4 formalization of [CORA](https://cora.in.tum.de), the Continuous
Reachability Analyzer.

## Installation

Follow the [Lean](https://lean-lang.org/) installation.

Lean works best in combination with [VS Code](https://code.visualstudio.com) with its [Lean 4 extension](https://marketplace.visualstudio.com/items?itemName=leanprover.lean4), 
which provides the goal view and diagnostics as you type:

Clone this repository and open it in VS Code.

  git clone https://gitlab.lrz.de/cps/CORALean.git

## Build

To build the project, run

```
cd lean && lake exe cache get && lake build
```


## Layout

Two halves. `lean/` holds the definitions and their proofs; `targets/` holds
one directory per language implementing actual code.

```
lean/
  src/           the formalization — definitions, theorems, proofs
targets/
  c/             Lean's own compiler output, copied out of .lake  (generated)
    src/                 the exported C, mirroring the Lean modules
    export-from-lake.sh  clean rebuild, then copy
  cpp/           written by hand against the Lean sources         (transcribed)
  ...
```

The C code is generated from Lean and serves as the reference.
Every other language should be generated or at least checked against the C implementation.

### The formalization

Mirrors CORA's structure and naming convention.

Set representations and their operations are defined over ℝ and proved
sound — e.g., each operation over-approximates the set it claims to.

Lean also formalizes the floating-point computations so it can be implemented in actual code (see the generated C code).
Thus, all theorems are first stated in ℝ under `lean/src/CORALean/Arithmetic/Real` and then refined in `.../Float`.
The floating-point layer assumes no format. `SoundFloatArithmetic F` asks only
for a real interpretation and arithmetic that rounds in a stated direction, so
its proofs hold for binary64 and for any other precision.
The proofs of `Float` then just refine the theorems in `Real`, which gives soundness by transitivity.


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

See [CONTRIBUTING.md](CONTRIBUTING.md) for tooling, file roles, the layering
rule, and the conventions proofs and docstrings follow.
