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
lake exe cache get && lake build
```


## Layout

The formalization lives in `src/CORALean/`, mirroring CORA's structure and
naming convention.

Set representations and their operations are defined over ℝ and proved sound —
each operation over-approximates the set it claims to. Every such theorem is
then refined for floating-point arithmetic by rounding "outward", which an
implementation can be tested against.


## Contributing

See [CONTRIBUTING.md](CONTRIBUTING.md) for the source layout, tooling, file
roles, the layering rule, and the conventions proofs and docstrings follow.
