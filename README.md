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


## The generated C

`lake build` also emits Lean's own C for every module, into `.lake/build/ir/`
along the module path: `src/CORALean/ContSet/Zonotope/Float/API.lean` becomes
`.lake/build/ir/CORALean/ContSet/Zonotope/Float/API.c`. It is a build product
and is not checked in — rebuilding is what keeps it in step with the sources.

Compile it with the toolchain's own `leanc`, which supplies the runtime headers
and links the Lean runtime and GMP:

```
"$(lean --print-prefix)/bin/leanc" -c .lake/build/ir/CORALean/ContSet/Zonotope/Float/API.c
```

Use that `leanc` rather than a system compiler: the C is written against the
runtime of the toolchain `lean-toolchain` pins, and other versions are not
expected to accept it.


## Layout

The formalization lives in `src/CORALean/`, mirroring CORA's structure and
naming convention.

Set representations and their operations are defined over ℝ and proved sound.
Nearly every operation over-approximates the set it claims to, and the float
layer refines each such theorem by rounding "outward" — computable for most of
that layer, but not all of it; see `Examples/ReachFloat.lean` for the split.

The Minkowski difference is the exception, and worth knowing about before
reading the interfaces: a difference is a *guarantee* — the states from which
everything still lands where it should — so an implementation may only ever
return a **subset**, and `MinkDiff` accordingly owes an inner approximation. Its
float counterpart rounds inward, the only operation in that layer which does.


## Findings

Formalizing turns things up. [FINDINGS.md](FINDINGS.md) tables the errors and
gaps found in the papers, and the places this formalization parts from CORA,
each pointing at the file that argues it.


## Contributing

See [CONTRIBUTING.md](CONTRIBUTING.md) for the source layout, tooling, file
roles, the layering rule, and the conventions proofs and docstrings follow.
