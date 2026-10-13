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
has its own `reachFloat` (`LinearSys`, `LinParamSys`, `NonlinearSys`, the hybrid
automaton), while discrete-time reachability needs none; see
`Examples/ReachFloat.lean` for the split.
Outside the set representations, the neural network layers among them, an
algorithm is written once over the scalar instead, and run at ℝ and at a
machine scalar alike.

The float layer fixes no format, and the same definition runs at any of its
scalars: `Dyadic p`, exact integer arithmetic at a `p`-bit significand whose
soundness obligations are theorems; `IEEE fmt`, the same at a real binary
format — binary64, binary32, binary16, OCP E4M3 or E2M1, subnormals included —
whose values past the format's range are detected and reported as overflow,
never silently continued; and native binary64, which is fast and whose
obligations are assumed instead, all ten as a single `TrustedHardware` axiom. Every `Float`
result carries that one name in `#print axioms`. The hardware instance is only trusted while all
values remain in the normal range of binary64: operations that overflow or underflow return NaN,
which propagates, so such runs can be detected. What exactly that covers, and the other
things a float result trusts, is under "The trust base of float and hardware results" below.

The Minkowski difference is the exception, and worth knowing about before
reading the interfaces: a difference is a *guarantee* — the states from which
everything still lands where it should — so an implementation may only ever
return a **subset**, and `MinkDiff` accordingly owes an inner approximation. Its
float counterpart rounds inward, the only operation in that layer which does.


## The trust base of float and hardware results

Everything a float or hardware result depends on beyond the Lean kernel is listed here, and
nowhere else. A result at `ℝ`, `Dyadic p`, `IEEE fmt` or `FixedPoint k` depends on none of it:
`#print axioms` shows only Lean's own.

### 1. The three axioms

CORALean declares exactly three `axiom`s, one per file; `scripts/check-axioms.lean` asks Lean
(`Lean.collectAxioms`) to confirm that no other exists.

| Axiom | File | Says | Status |
|---|---|---|---|
| `Binary64.trustedHardware` | `src/CORALean/Global/Float/Instances/Binary64/Definitions/Axioms.lean` | The ten conjuncts of `TrustedHardware` (`.../Definitions/TrustedHardware.lean`): native `Float` negation, `minimum`, `maximum`, `≤`, `0.0`, `1.0`, `half`, and the upward `addUp`, `mulUp`, `divUp` (positive divisor) are what `SoundFloatArithmetic` asks of a scalar, read through `Binary64.toReal`. | The library's own: every `Float` result carries it. **False as a proposition** outside the normal range (below). |
| `Flint.trustedFlint` | `.../Instances/Flint/Definitions/Axioms.lean` | FLINT's directed `arf_add`/`arf_mul`/`arf_div` round as documented, and the C shim's `Int`/`fmpz` conversion is exact. | True of FLINT; **opt-in**: reached only by `bench-flint` and `Examples/BenchFlint.lean`. |
| `Bench.nearestUnsound` | `src/CORALean/Examples/Bench/NearestUnsound/Axioms.lean` | Round-to-nearest rounds in the direction an operation's name says. | **False by design**, **bench-only**: it exists to run the unchanged library on CORA's own arithmetic. A result that reaches it proves nothing. |

`sh scripts/check-axioms.sh` keeps the last two out. It asserts that these three are the only axioms
declared; that the named headline guarantees do not reach `nearestUnsound`; that no declaration of
any library module outside `Examples/Bench/` reaches `nearestUnsound`, and none outside the FLINT
backend and its bench reaches `trustedFlint`; that the two unsound instantiations and the FLINT one
do reach theirs (positive controls, so the sweep is not vacuous); and that the oracle's entry
declarations reach neither. `scripts/check-conventions.sh` additionally refuses the import that
would let `NearestUnsound` in. Nothing keeps `trustedHardware` out: it is the library's one
assumption, and what this section is about.

### 2. `trustedHardware` is false outside the normal range, and a hardware run is sound anyway

`Float` is opaque, so the axiom can only be stated about the bits, through `toReal`, which reads
any pattern, an infinity or a NaN included, as `m · 2 ^ e`: `+∞` is `2 ^ 1024`, and a NaN is
`1.5 · 2 ^ 1024` (Lean's `toBits` reports every NaN as the one pattern `0x7FF8…`). Stated
unconditionally the axiom is therefore false. `lake exe hardwarecheck` shows this: of the samples
whose result the model puts outside the normal range, the `litFalse` column counts those where the
axiom's inequality, read on the NaN's decoding, fails (for `mulUp`, `divUp`, `half`, `addUp`, and
`neg` of a NaN). The results are claimed sound by a meta-level argument, not a theorem:

> If the final value contains no NaN, every instance of `trustedHardware` that the proof used is
> true.

*What it relies on.* Each step was checked against the code.

1. **Gating.** Every rounded operation returns NaN unless its result is in range
   (`Binary64/Operations/InRange.lean`, `StepUp.lean`). `addUp`, `addDown`, `mulUp`, `mulDown`,
   `divUp`, `divDown` pass the machine result through `stepUp`, which keeps a zero, and otherwise a
   normal float whose one-ulp step is also normal, and returns NaN for a subnormal, an infinity or a
   NaN. `mulUp` and `divUp` also return NaN where the machine result is zero and the exact one is not
   (`a, b ≠ 0` for the product, `a ≠ 0` for the quotient). `half` is NaN unless the result is normal
   or an exact zero. So a non-NaN result of a rounded operation is a zero or a normal float, and the
   instance of its conjunct at those operands is true on IEEE 754 binary64.
2. **Propagation.** A NaN input gives a NaN output in every one of them (`NaN + x`, `NaN * x`,
   `NaN / x` are NaN and `stepUp` and `inRange` refuse a NaN), and so do `neg` (the sign flips; it
   stays a NaN) and `minimum`/`maximum` (an unordered pair returns `a + b`). An infinity input is
   absorbed likewise, except `divUp 0 (+∞) = 0`, which is exact. Hence a non-NaN float has only
   non-NaN ancestors: if the output holds no NaN, no operation in its dependency cone received or
   produced one.
3. **Tests.** `≤` on a NaN is false. A branch taken on `a ≤ b` is the only thing the class lets a
   proof use about it (`toReal_le_of_le`, the true direction), and a true `a ≤ b` has non-NaN
   operands, which by 2 have non-NaN ancestors. The unrounded conjuncts (`neg`, `minimum`,
   `maximum`, `≤`, `0.0`, `1.0`) are true on every non-NaN pattern, infinities included, because
   `toReal` is monotone and sign-symmetric there.
4. **The final check.** A reported value is trusted only if it holds no NaN. For the entry points
   that have a `…Checked` form (below) the library makes this test itself; for any other it is the
   caller's, since the unchecked theorems conclude about `some Rs` whatever `Rs` holds. The bench records one (`overflows` in `Examples/Bench/NumberType.lean`,
   `nonFinite` flags and `overflowStep` in the output; a stderr line in `Timing.lean`, `Nn.lean`
   and `Mnist.lean`), and prints a NaN as `"NaN"`. A verdict decided by `≤` tests rejects a NaN among the operands it
   compares by itself, by 3; a value it does not compare is not covered by that.
5. **The proof's shape.** The proof of the guarantee used the axiom only at the operands of
   operations the run performed, on the dependency cone of the output and of the true tests. This
   is a property of how the library's proofs go (structural induction on the definitions, one
   field per operation), read off the code, not enforced by the kernel: nothing stops a proof from
   instantiating a field at a float the run never computed.

*What it does not cover.*

* **The machine.** That an instance with in-range operands is true is `TrustedHardware`'s content
  and is sampled, not proved, by `hardwarecheck` (a sample, on the CI machine and compiler). It
  assumes round-to-nearest-even, no extended precision, no fused multiply-add contraction and no
  fast-math in the code the compiler emits for `Binary64`'s operations. See 4.
* **A NaN that is read as a number, at the sites that are only argued.** `ToRat.toRat` and
  `toReal` decode a NaN to the finite rational `1.5 · 2 ^ 1024`. `ToRat.isNaN` tells it apart, and
  the decisions in ℚ that bear on soundness test it: `adaptiveStepFloat` (the step and its norm
  bound), `Ellipsoid.ellipsoidNormUb`, `SpectraShadow.dualCertified` and `representsa_emptySet`
  reject a NaN among the floats they read. The other `toRat` sites are tuning or proposal only
  (`AdaptSetOrder(Loop)`, `AdaptTimeStepFloat`, `AdaptTimeStepOrderFloat`,
  `AdaptTimeStepSearchFloat`, the `HPolytope` and `ConZonotope` LP weights and the `isDisjointLP`
  separator): their results are re-checked by a decision above, or by a float checker that accepts
  any weights, and the theorems hold for any tuning choice, so a NaN there costs tightness only.
  This is read against the theorems, not a separate proof. The `Reach.steps` calls in the
  `reach*Float` functions read a NaN `Δt` as `1.5 · 2 ^ 1024`; a step count of one or more
  then needs `tFinal − tStart` to be a multiple of that, and any step run returns NaN floats, which
  the `…Checked` entry points reject. That last point is argued, not proved.
* **The final NaN check covers only the entry points that have a `…Checked` form.**
  `LinearSys.reachFloatChecked`, `reachWrappingFreeFloatChecked`,
  `reachTimePointWrappingFreeFloatChecked`, `reachFloatInputChecked`, `reachAdaptiveFloatChecked`,
  `LinParamSys.reachFloatChecked`, `NonlinearSys.FloatModel.reachFloatChecked`,
  `NonlinearSys.FloatHessModel.reachAlgFloatChecked`, `NonlinDASys.reachFloatChecked`,
  `NonlinParamSys.reachFloatChecked`, `Location.reachFloatChecked`,
  `HybridAutomaton.reachFloatChecked`, `ParallelHybridAutomaton.reachFloatChecked` and
  `NeurNetContrSys.reachFloatChecked` return `none` if a float of
  the result is a NaN (`checkNoNaN`, `Global/Float/NoNaN.lean`), and each `…Checked_eq_some` says a
  `some` is the unchecked `some`. A `Bool`, `Nat` or
  `ℚ` derived from a float is covered only where the deriving function tests for NaN, as the four
  named in the item above do.
* **NaN inputs.** `hardwarecheck` does not claim the axiom for them, and neither does this section. `ellipsoidNormUb`, `dualCertified`, `representsa_emptySet` and
  `adaptiveStepFloat` return `none` or `false` on one.
* **Subnormal inputs** are covered (`toReal` reads them exactly) but a subnormal *result* is NaN,
  so a run that needs the subnormal range is rejected, not trusted.

### 3. `NonlinearSys.FloatModel.Encloses`

`NonlinearSys.FloatModel` (`src/CORALean/ContDynamics/NonlinearSys/Definitions/FloatModel.lean`)
is the interval extension of the field `f` and of its two Jacobian blocks that a float run
evaluates in place of `f`. `FloatModel.Encloses fm sys` (same file, lines 51-60) says `fm.f X U`
holds `sys.f` over every box and the Jacobian boxes hold the slope between any two points of it.
`reachFloat_outer` (`.../Theorems/ReachFloatOuter.lean`) and every theorem about
`reachFloat`/`relinRunFloat` take it as a **hypothesis**. It is **user-supplied and unchecked**: a
`FloatModel` is a function, and no run compares it with `f`. A wrong model gives a correct-looking
`reachFloat` result that encloses nothing. (`NonlinearSysDT.FloatModel.Encloses` and
`NonlinearARX.FloatModel.Encloses` are the same hypothesis for the discrete-time classes.)

It is discharged by a Lean proof about the model, against the scalar's own obligations:
`FloatModel.Encloses.of_hasFDerivAt` (`.../Theorems/EnclosesOfHasFDerivAt.lean`) reduces it to the
function boxes holding `f` and the Jacobian boxes holding the derivative at every point of the box;
for a polynomial field the slope is plain algebra. One example discharges it:
`vdpModel_encloses` and `vdpHessModel_encloses` in `src/CORALean/Examples/RunnableFloat.lean`, for
Van der Pol at `Dyadic 24`, where the proof uses only theorems. No example discharges it at
hardware `Float`, and no other example in `src/CORALean/Examples` builds a `FloatModel`. A
model at `Float` would have to be proved against `trustedHardware`, and so carries its qualification.

### 4. The compiled path

What is verified is the Lean definition: the kernel checks that the definition satisfies the
theorem. What runs is something else. Lean's code generator turns the definition into C
(`.lake/build/ir/`, see above), a C compiler turns that into machine code, and the Lean runtime
supplies `Float`, `Int` and `Nat` arithmetic, `Float.toBits`/`ofBits`, GMP. All three are
unverified, and nothing here proves the compiled code computes the definition's value. The
`Float` path additionally depends on the machine's rounding mode and on the compiler not
reassociating or fusing the operations. The only check is sampling: `hardwarecheck` linked
against the emitted C. `lake env lean --run` runs the toolchain's precompiled primitives
instead, and tests less.

### 5. The oracle serves only software scalars

`lake exe oracle` resolves every request's `dtype` in `withDtype`
(`src/CORALean/Examples/Oracle/Dtype.lean`): `binary64` and `ieee:binary64` are the axiom-free
`IEEE .binary64`, never hardware `Float`; the others are `IEEE .binary32/.binary16/.e4m3/.e2m1`,
`Dyadic p` and `FixedPoint k`. No arm instantiates `Float`, `Flint` or a nearest-rounding scalar,
and `scripts/check-axioms.sh` checks that the oracle's entry declarations reach neither
`nearestUnsound` nor `trustedFlint`. The hardware `Float` path is the `bench` executable
(`--type float`) and `hardwarecheck`.

## Testing the hardware axiom

`TrustedHardware` is trusted, not proved, so `lake exe hardwarecheck [--seed N] [--n N]` samples it:
every native operation (`addUp`, `mulUp`, `divUp` and their `Down`s, `half`, `neg`, `minimum`,
`maximum`, `≤`, the literals `0.0` and `1.0`) is compared, exactly, with the axiom-free `IEEE .binary64`
on random bit patterns and structured inputs (zeros, subnormals, both ends of the range, ties,
cancellation, `1 ± ulp`, operands about `2 ^ 53` apart), and must return NaN exactly outside the
normal range. It checks the soundness bound and that the step is no more than one. It prints the first
failing input per operation and exits `1` on a violation. This is a **sample**, not a proof, and
covers the machine and compiler it runs on: CI runs it linked, on Linux, as
`lake build hardwarecheck && .lake/build/bin/hardwarecheck`. Linking is what makes it test the C lake
emits from our definitions; `lake env lean --run src/CORALean/Examples/HardwareCheck.lean` runs the
toolchain's precompiled primitives instead. Not covered: NaN inputs, where `toReal (-a) = -toReal a` and
the other conjuncts are false as stated (Lean's `toBits` reports every NaN as one pattern), and other
platforms or compilers.

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
mismatch by exact value. `lake exe flintcheck` (`Examples/FlintCheck.lean`)
checks `trustedFlint` itself, against exact rationals rather than `Dyadic p`'s
code: for random and structured operands (bit lengths around `p`, ties,
cancellation, a far-smaller addend that only matters as a sticky bit) at
`p` from 2 to 200, each directed `arf_add`/`arf_mul`/`arf_div` result must lie
on the claimed side of the exact value, have at most `p` significant bits, and
equal the nearest such number on that side; and `a + 0`, `a * 1` must return a
mantissa past `2^64` and an exponent past `2^64` unchanged, which is the shim's
`Int`/`fmpz` conversion. It exits non-zero on any violation. Linking FLINT is
what makes this a CI job of its own, `flint-check`: it builds FLINT, runs
`flintcheck`, `bench-flint selftest` and a one-repetition `headline-a`, on
schedules, on a merge request touching the backend or its scripts, and on
request (manual) for any other. No violation has been found (last run locally:
FLINT 3.6.0, about 150,000 comparisons per run, seed `20261008`); the job is what
keeps that a checked claim rather than a local one.

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
