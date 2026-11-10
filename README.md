# CORALean 🪸

A Lean 4 formalization of [CORA](https://cora.in.tum.de), the Continuous Reachability Analyzer. 

Paper reference: `CORALean: A Lean 4 Formalization of CORA. Tobias Ladner, Matthias Althoff. TBD. 2026.`

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

Afterwards, all experiments of the paper can be run using the compiled C code (details in [experiments/](experiments/README.md)):

```
sh experiments/repeatability.sh
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
scripts/              convention checks and tooling (see scripts/README.md)
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

The default backend is `IEEE`, which is also used in the paper's experiments.

### The trust base

`Hardware` rests on the axiom `trustedHardware`, and that axiom is false. It states the ten obligations of `SoundFloatArithmetic` for every input, and no format with finitely many values meets them: `not_isTrustedHardware` proves this, so the axiom proves `False`, and a theorem at `Hardware` is no guarantee on its own. What a `Hardware` run rests on instead:

1. Each obligation is true of IEEE 754 binary64 wherever its result is a number (the field docstrings in `IsTrustedHardware.lean` say where each one fails). Every rounded operation returns NaN outside the normal range, and NaN propagates through the rounded operations, `minimum` and `maximum`. `lake exe hardwarecheck` samples both, at the range edges included.
2. The result holds no NaN. `checkNoNaN` (`Global/Float/NoNaN.lean`) tests this, and every `reach…Checked` entry point applies it.
3. From 1 and 2 to "every operation of the run was a true instance" is an informal argument, not a theorem. It fails where a NaN is dropped rather than propagated, e.g. by a comparison (`≤` with a NaN is `false`) that picks a branch.

This is intended: `trustedHardware` stands for the machine's IEEE 754 behaviour inside the normal range, stated unconditionally because `SoundFloatArithmetic` has no validity predicate. `Hardware` is the fast backend; for a guarantee that is a theorem, use `IEEE` or `Dyadic`. Another backend is selected with `--type`:

```
lake exe bench <experiment> --type ieee|dyadic|hardware|nearest|fixed
```

The `Flint` backend uses the [FLINT library](https://flintlib.org) to run the code at arbitrary precision. 
This can be optionally enabled by running:
```
bash scripts/build/install-flint.sh       # once: GMP, MPFR, FLINT into $HOME/.local/flint-prefix
bash scripts/build/build-flint-shim.sh    # into .lake/flint/libcoralean_flint.a
lake build bench-flint
```


## Contributing

See [CONTRIBUTING.md](CONTRIBUTING.md) for details on the source layout, tooling, file roles, the layering rule, and the conventions proofs and docstrings follow.

