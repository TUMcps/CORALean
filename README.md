# CORALean 🪸

A Lean 4 formalization of [CORA](https://cora.in.tum.de), the Continuous Reachability Analyzer. 

Paper reference: CORALean: A Lean 4 Formalization of CORA. Tobias Ladner, Matthias Althoff. `TBD`. 2026.

## Formalizing CORA in Lean 4

The goal of this project is to formalize the research behind CORA as well as to provide a sound ground-truth implementation.
A list of formalized papers can be found in [references/](references/README.md) detailing the formalization of each publication.
The formalization of the Matlab implementation is detailed in [references/coverage](references/coverage/README.md).
You can check the current status using (see script for details): 

```
python3 scripts/formalization-stats.py
```

CORA was largely formalized autonomously using AI agents,
where we used Claude Opus 5+ as the main worker and Claude Fable 5+ conducting independent reviews.
To ensure correctness and maintain structure in the project, >5% of all files are manually reviewed by the authors (see `python scripts/review.py --status`).
Details can be found in the paper.


## Installation

Follow the [Lean](https://lean-lang.org/) installation. <br/>
Lean works best in combination with [VS Code](https://code.visualstudio.com) and its [Lean 4 extension](https://marketplace.visualstudio.com/items?itemName=leanprover.lean4), 
which provides diagnostics and open goals in the Lean InfoView as you type.

Then, clone this repository:

```
git clone https://gitlab.lrz.de/cps/CORALean.git
```

and open it in VS Code. Finally, to build the project, run

```
lake exe cache get && lake build
```


## Layout

```
src/CORALean/
├── ContSet/          set representations (Zonotope, Interval, PolyZonotope, ...)
│   └── Zonotope/
│       ├── Real/     definitions, operations and soundness theorems over ℝ
│       └── Float/    runnable float operations, refining the ones over ℝ
├── ContDynamics/     continuous-time systems and their reachability (LinearSys, NonlinearSys, ...)
├── DiscrDynamics/    discrete abstractions (MarkovChain, GridPartition)
├── HybridDynamics/   hybrid automata
├── NN/               neural networks and their layers
├── Specification/    specifications (STL, RTL, ...)
├── Global/           shared mathematics and the float scalars (Global/Float/)
└── Examples/         runnable examples, benchmarks, the oracle
references/           one page per publication: its results and where they are formalized
experiments/          the paper's experiments
scripts/              convention checks and tooling
```

The structure and naming mirror CORA. 


## Verified C Code

`lake build` also emits C for every module into `.lake/build/ir/` for all runnable code.
In particular, this includes all classes and operations refined to the floating-point level.
The C code can be compiled with `leanc`, which matches the runtime the C is written and verified against:

```
"$(lean --print-prefix)/bin/leanc" -c .lake/build/ir/CORALean/ContSet/Zonotope/Float/API.c
```

This code can be used as a ground-truth implementation as it is proven to be safe in Lean.

### Floating-Point Model and FLINT Backend (optional)

When running the C code, one can use multiple backends to represent the floating-point numbers with precision $p$.

| Instance | $p$ | Exponent | Rounding | Axioms |
|---|---|---|---|---|
| `Nearest` | 64 | bounded | nearest | ✗ unsound |
| `IEEE` | 4–64 | bounded, subnormals | outward | Lean axioms |
| `Hardware` | 64 | normal range | nearest + 1 ulp | + `trustedHardware` |
| `Dyadic` | 4–64 | unbounded | outward | Lean axioms |
| `Flint` | 4–64 | unbounded | outward | + `trustedFlint` |
| `FixedPoint` | – | none, $f$ decimal digits | outward | Lean axioms |

The `Flint` backend uses the [FLINT library](https://flintlib.org) to run the code at arbitrary precision. 
This can be optionally enabled by running:
```
bash scripts/install-flint.sh       # once: GMP, MPFR, FLINT into $HOME/.local/flint-prefix
bash scripts/build-flint-shim.sh    # into .lake/flint/libcoralean_flint.a
lake build bench-flint
```


## Contributing

See [CONTRIBUTING.md](CONTRIBUTING.md) for details on the source layout, tooling, file roles, the layering rule, and the conventions proofs and docstrings follow.

