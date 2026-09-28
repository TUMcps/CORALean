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
layer refines each such theorem by rounding "outward" — and runs: every float
operation is a `def`, save the interface instantiated at ℝ itself, which is a
specification proxy rather than a representation. Continuous-time reachability
has no float counterpart at all; see `Examples/ReachFloat.lean` for the split.
Outside the set representations, the neural network layers among them, an
algorithm is written once over the scalar instead, and run at ℝ and at a
machine scalar alike.

The float layer fixes no format, and the same definition runs at any of its
scalars: `Dyadic p`, exact integer arithmetic at a `p`-bit significand whose
soundness obligations are theorems; `IEEE fmt`, the same at a real binary
format — binary64, binary32, binary16, OCP E4M3 or E2M1, subnormals included —
whose values past the format's range are detected and reported as overflow,
never silently continued; and native binary64, which is fast and whose
obligations are assumed instead — all ten as a single `TrustedHardware` axiom in
`Global/Float/Instances/Binary64/Definitions/Axioms.lean`, the only file here that assumes
anything. Every `Float` result carries that one name in `#print axioms`. The
hardware instance is only trusted while all values remain in the normal range of
binary64; operations that overflow or underflow return NaN, which propagates to
the result, so such runs are detected at run time.

The Minkowski difference is the exception, and worth knowing about before
reading the interfaces: a difference is a *guarantee* — the states from which
everything still lands where it should — so an implementation may only ever
return a **subset**, and `MinkDiff` accordingly owes an inner approximation. Its
float counterpart rounds inward, the only operation in that layer which does.


## FLINT backend (optional)

A third scalar, `Flint p` (`Global/Float/Instances/Flint/`): the same
`(mantissa, exponent)` pair `Dyadic p` is, but its six rounded operations call
[FLINT](https://flintlib.org)'s `arf_add`/`arf_mul`/`arf_div` through a small C
shim rather than pure Lean, so an algorithm runs at arbitrary precision without
paying `Dyadic`'s big-integer cost in Lean itself. It is opt-in: nothing in the
default `lake build`, including the default `bench` executable, needs FLINT to
compile or link — the Flint instances elaborate as a second root of the
`CORALean` library (proofs checked on every commit) but are imported by no
default executable.

Building it needs FLINT, MPFR and GMP newer than the ones Lean's own runtime
links statically, so they are built into a private prefix and combined into
one archive whose only global symbols are the shim's own, keeping the two GMPs
from ever meeting at link time:

```
bash scripts/install-flint.sh       # once: GMP 6.3.0, MPFR 4.2.2, FLINT 3.6.0
                                     # into $HOME/.local/flint-prefix
bash scripts/build-flint-shim.sh    # combines them into .lake/flint/libcoralean_flint.a
lake build bench-flint              # or: lake exe bench-flint <experiment> --type flint ...
```

`bench-flint selftest` differential-tests `Flint p` against `Dyadic p` at every
op, precision and a few thousand pseudo-random operands (including values past
`2^64` and negative, to exercise the FFI's `Int` conversion), and reports any
mismatch by exact value — none found so far.

The one thing trusted beyond `Dyadic p`'s own theorems is `trustedFlint`
(`Global/Float/Instances/Flint/Definitions/Axioms.lean`): that FLINT's directed
rounding does what its documentation says, and that the shim's `Int`/`fmpz`
conversion is exact. `scripts/check-axioms.sh` keeps it out of every result
outside this backend and `Examples/BenchFlint.lean`, the way it keeps the
bench's false `nearestUnsound` out of the library.


## What is formalized

[references/](references/README.md) holds a page per publication this draws on,
listing that paper's results and, for each, where it is formalized — so whether
a given proposition is done is a lookup rather than a search. The page's counts
are of the paper, so they do not move when we do more work.


## Findings

Formalizing turns things up. An error found in a paper is recorded on that
paper's page under [references/](references/README.md), beside the result it is
about. [FINDINGS.md](FINDINGS.md) is the other half: the places this
formalization parts from CORA on purpose, each pointing at the file that argues
it.


## Contributing

See [CONTRIBUTING.md](CONTRIBUTING.md) for the source layout, tooling, file
roles, the layering rule, and the conventions proofs and docstrings follow.
