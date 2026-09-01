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

```
lean/            the formalization — definitions, theorems, proofs
targets/         one directory per language implementing actual code
  c/             Lean's own compiler output, copied out of .lake  (generated)
  cpp/           written by hand against the Lean sources         (transcribed)
```

The setup mirrors CORA's structure and naming convention.
Set representations and their operations are defined over ℝ and proved sound — e.g., each operation over-approximates the set it claims to.
Every such theorem is then refined for floating-point arithmetic by rounding "outward", which an implementation can be tested against.

The C code is generated from Lean and serves as the reference.
Every other language should be generated or at least checked against the C implementation.


## Contributing

See [CONTRIBUTING.md](CONTRIBUTING.md) for the source layout, tooling, file roles, the layering rule, and the conventions proofs and docstrings follow.
