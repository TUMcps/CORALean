# Findings

Where formalizing turned something up: an error or a gap in a source, or a place
this formalization deliberately parts from CORA. A line each — the linked file's
module docstring carries the argument.

**What belongs here.** Settled facts, which will not change: a source is wrong,
or this formalization does something differently on purpose. Anything with work
still to do goes to the issue tracker instead, under its label. A finding can
give rise to both — the error is recorded here, the fixing of it is an issue.

## Errors and omissions in the sources

| Where | What is wrong or missing | Details |
|---|---|---|
| Althoff's thesis, Prop. 3.1 — the tail | The printed proof pulls one `[−1,1]` out of two independent remainders, and the bound does not follow; the proposition holds for another reason. | [`CorrectionMatrix.lean`](src/CORALean/ContDynamics/LinearSys/MatExp/Theorems/CorrectionMatrix.lean), [`ExpDiff.lean`](src/CORALean/ContDynamics/LinearSys/MatExp/Theorems/ExpDiff.lean) |
| AAAI'24 exponent relaxation, `prop:exp-relax-single` | The centre shift reads `+ξ_E/2`; it is `−ξ_E/2`. And the evenness of `E_{k₀,j}` is omitted, without which the shift is zero. CORA is unaffected by either. | [`RelaxExp.lean`](src/CORALean/ContSet/PolyZonotope/Real/Operations/RelaxExp.lean) |
| ICML'25 "Explaining Fast and Slow", §4 | The transfer theorem's converse fails, even under its own containment hypothesis. | [`SuffExplanationConverseFails.lean`](src/CORALean/NN/Theorems/SuffExplanationConverseFails.lean) |
| HSCC'23 abstraction refinement | Convergence needs a Lipschitz bound on every network tail. | [`PropagateAtInflate.lean`](src/CORALean/NN/Theorems/PropagateAtInflate.lean) |
| HSCC'23 sensitivity analysis | Needs differentiability per layer; differentiability of the network's evaluation does not suffice. | [`EvalDifferentiable.lean`](src/CORALean/NN/Theorems/EvalDifferentiable.lean) |

## Where the formalization parts from CORA or its sources

| Subject | What differs | Details |
|---|---|---|
| Homogeneous time-interval step | `linComb` in place of CORA's convex hull, so a non-convex representation keeps its shape. | [`TimeIntervalStep.lean`](src/CORALean/ContDynamics/LinearSys/Operations/TimeIntervalStep.lean) |
| `ConPolyZono`'s constraints | `b` is an `Interval` where the source writes an equality, which has no direction to round in. | [`ConPolyZono.lean`](src/CORALean/ContSet/ConPolyZono/Real/ConPolyZono.lean) |
| Abstraction error of a linearization | `A` and `B` need not be the Jacobians; any pair admits a certificate. | [`AbstractionError.lean`](src/CORALean/ContDynamics/NonlinearSys/AbstractionError.lean) |
| Float `Zonotope.reduceGirard` | `sortPerm` in place of `Tuple.sort`: no float type is a `LinearOrder`. | [`ReduceGirard.lean`](src/CORALean/ContSet/Zonotope/Float/Operations/ReduceGirard.lean) |
| `PolyZonotope.mul` | Exactness is over `point`, not `construct`. | [`MulExact.lean`](src/CORALean/ContSet/PolyZonotope/Real/Theorems/MulExact.lean) |
| Input reachability, Prop. 3.2 | Stated there as an equality; only `⊇` is proved, the direction the enclosures need. | [`InputReachSeparation.lean`](src/CORALean/ContDynamics/LinearSys/Theorems/InputReachSeparation.lean) |
| Input solution over a time interval | The split of the input set is a hypothesis, not something `ContSet` can compute. | [`InputSolutionTimeIntervalOuterSplit.lean`](src/CORALean/ContDynamics/LinearSys/Theorems/InputSolutionTimeIntervalOuterSplit.lean) |
