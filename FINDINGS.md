# Findings

Where formalizing turned something up: an error or a gap in a source, or a place
this formalization deliberately parts from CORA. One line each — the linked
file's module docstring carries the argument.

## Errors and omissions in the sources

| Where | What is wrong or missing | Details |
|---|---|---|
| Althoff's thesis, Prop. 3.1 — the tail | **The printed proof is unsound.** It concludes `E(t) − (t/r)E(r) ⊆ E(r)` by pulling a single `[−1,1]` out of both remainders; read as two independent interval matrices that difference has radius `Φ(t) + (t/r)Φ(r)`, twice what `E(r)` allows at `t = r`. The proposition itself holds — never splitting the remainders leaves one series sharing `A^i`, and `\|t^i − t·r^(i−1)\| ≤ r^i` on `[0,r]` gives the proposition's own bound. CORA argues the integrated remainder `Ê` the same way in `Documentation/inputErrorBounds`. | [`CorrectionMatrix.lean`](src/CORALean/ContDynamics/LinearSys/MatExp/Theorems/CorrectionMatrix.lean), [`ExpDiff.lean`](src/CORALean/ContDynamics/LinearSys/MatExp/Theorems/ExpDiff.lean) |
| AAAI'24 exponent relaxation, `prop:exp-relax-single` | The centre shift reads `+ξ_E/2`; it is `−ξ_E/2`. With both exponents even and `A > B`, `α^A − α^B ≤ 0`, so the difference interval is one-sided below zero. CORA is unaffected — it takes the midpoint numerically rather than from the proposition. | [#71](https://gitlab.lrz.de/cps/CORALean/-/issues/71) (not yet formalized) |
| AAAI'24 exponent relaxation, `prop:exp-relax-single` | The statement omits that the surviving generator's exponent column is even. CORA enforces it, but across two conditions in two functions, neither of which alone is the hypothesis. | [#71](https://gitlab.lrz.de/cps/CORALean/-/issues/71) |
| ICML'25 "Explaining Fast and Slow", §4 | The transfer theorem's converse fails *even granting its containment hypothesis*: a sound abstraction can be too loose to see a separation the original network has. | [`SuffExplanationConverseFails.lean`](src/CORALean/NN/Theorems/SuffExplanationConverseFails.lean) |
| HSCC'23 abstraction refinement | Convergence of the loop needs a Lipschitz bound on every network tail. A per-layer error limit alone says nothing at the output, since a later layer amplifies an earlier layer's residual. | [`PropagateAtInflate.lean`](src/CORALean/NN/Theorems/PropagateAtInflate.lean) |
| HSCC'23 sensitivity analysis | Sensitivity needs differentiability *per layer*; differentiability of the network's own evaluation does not suffice. A linear layer with `W = 0` after a ReLU is differentiable everywhere while the ReLU under it is not. | [`EvalDifferentiable.lean`](src/CORALean/NN/Theorems/EvalDifferentiable.lean) |

## Where the formalization parts from CORA or its sources

| Subject | What differs | Details |
|---|---|---|
| `polyZonotope/relaxExponents` | CORA's third branch over-approximates (`d = du − dl`, no shift) where the exact centre shift would do. `dc + [−d, d] = [dl, du]` is an identity, so the evenness test gates tightness, not soundness — an improvement available in CORA itself. | [#71](https://gitlab.lrz.de/cps/CORALean/-/issues/71) |
| Homogeneous time-interval step | `linComb` in place of CORA's `CH(X₀, e^{Ar}X₀)`, so a non-convex representation keeps its shape instead of being hulled. | [`TimeIntervalStep.lean`](src/CORALean/ContDynamics/LinearSys/Operations/TimeIntervalStep.lean) |
| `ConPolyZono`'s constraints | `b` is an `Interval` where Kochdumper and Althoff write `A μ(α) = b`. An equality has no direction to round in, so no float layer could compute a constraint at all. | [`ConPolyZono.lean`](src/CORALean/ContSet/ConPolyZono/Real/ConPolyZono.lean) |
| Abstraction error of a linearization | `A` and `B` are *not* required to be the Jacobians at the expansion point: any pair admits a certificate, a bad pair only making `L` large. That covers a linearization computed in float arithmetic, or reused across steps as CORA does, with no claim about the true derivative. | [`AbstractionError.lean`](src/CORALean/ContDynamics/NonlinearSys/AbstractionError.lean) |
| Float `Zonotope.reduceGirard` | No float type is a `LinearOrder` — distinct representations of one value compare equal each way — so the ranking uses `sortPerm`, which asks its comparator for nothing. Sound because `reduceBy_outer` holds at every partition. | [`ReduceGirard.lean`](src/CORALean/ContSet/Zonotope/Float/Operations/ReduceGirard.lean) |
| `PolyZonotope.mul` | Exactness is over `point`, not `construct`: `construct (mul S₁ S₂)` is not `construct S₁ * construct S₂`, both being functions of one shared factor vector. At `S₁ = S₂ = [−1, 1]` the shared-factor product is `[0, 1]` and the product of the sets is `[−1, 1]`. | [`MulExact.lean`](src/CORALean/ContSet/PolyZonotope/Real/Theorems/MulExact.lean) |
| Input reachability, Prop. 3.2 | The thesis states an equality; only `⊇` is proved, that being the direction the enclosures use and the one that has to build an input rather than take one apart. | [`InputReachSeparation.lean`](src/CORALean/ContDynamics/LinearSys/Theorems/InputReachSeparation.lean) |
| Input solution over a time interval | Althoff's second case is stated with the split of the input set as a *hypothesis*: `ContSet` cannot name a centre, so which constant and which sets is the representation's business. | [`InputSolutionTimeIntervalOuterSplit.lean`](src/CORALean/ContDynamics/LinearSys/Theorems/InputSolutionTimeIntervalOuterSplit.lean) |
| `ConZonotope.linComb` and `reduce` | Both go through the enclosing zonotope and give the constraints up — precision CORA does not lose. A known gap, not a design choice. | [`Operations/API.lean`](src/CORALean/ContSet/ConZonotope/Real/Operations/API.lean) |
