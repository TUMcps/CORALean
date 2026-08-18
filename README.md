# CORALean 🪸

A Lean 4 formalization of [CORA](https://cora.in.tum.de), the Continuous
Reachability Analyzer.

## Installation

Follow the [Lean](https://lean-lang.org/) installation. <br/>
Lean works best in combination with [VS Code](https://code.visualstudio.com) and its [Lean 4 extension](https://marketplace.visualstudio.com/items?itemName=leanprover.lean4), 
which provides diagnostics and open goals in the Lean infoView as you type.

Then, clone this repository:

```
git clone https://gitlab.lrz.de/cps/CORALean.git
```

and open it in VS Code. Finally, to build the project, run

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

The setup mirrors CORA's structure and naming convention.
In general, all set representations and their operations are defined over ℝ and proved sound — e.g., each operation over-approximates the set it claims to.
These proofs can be found under `lean/src/CORALean/Arithmetic/Real`.

Lean also formalizes the floating-point computations by soundly rounding "outward" to remain sound.
Thus, all theorems first stated in ℝ are refined in `lean/src/CORALean/Arithmetic/Float` to deal with floating point arithmetic.
This refinement can then be used to test any implementation against.


```
lean/src/CORALean/
  Global/          shared: array types, the scalar, index partitions, Mathlib
  Arithmetic/
    Real/          the specification: exact arithmetic over ℝ
      ContSet/     one directory per concept
        ContSet/   the interface every representation instantiates
        Interval/  Interval.lean (the type), Operations/ (one per operation),
                   Theorems/ (one per guarantee),
                   Instances.lean (the interface, instantiated),
                   API.lean (the whole directory, and nothing but imports)
        ...
      ContDynamics/  algorithms, written against the interface alone
        LinearSysDT/ discrete-time linear systems, and reachability
    Float/         the refinement: the same representations, rounded
      FloatOps / SoundFloatArithmetic   operations, then their guarantees
      Instances/   Dyadic (outward rounding)  Real (trivial)
      ContSet/
        InflatedContSet/   nominal part + error box, and its shared lemmas
        Interval/  Floating point formalization of Interval in Real
        ...
```


## Contributing

See [CONTRIBUTING.md](CONTRIBUTING.md) for tooling, file roles, the layering rule, and the conventions proofs and docstrings follow.
