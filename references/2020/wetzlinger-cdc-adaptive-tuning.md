# Adaptive parameter tuning for reachability analysis of linear systems

M. Wetzlinger, N. Kochdumper and M. Althoff. "Adaptive parameter tuning for reachability
analysis of linear systems". CDC, 2020, pp. 5145–5152.

**Source:** https://arxiv.org/pdf/2006.12091 — the arXiv preprint of the CDC paper, read with `pypdf` (poppler is not installed here, so the Read tool's PDF-page mode is unavailable). The table was seeded from https://ar5iv.labs.arxiv.org/html/2006.12091, whose numbering is not to be trusted; every locator below has since been re-read off the PDF and none of them moved.  
**Inventory:** confirmed

Every tuning knob a reachability run has — the time step, the order a set is
reduced to, how the error budget is split — chosen against a stated tolerance
instead of guessed. `reduceBoxOrder`, the step selectors and `reachOrders` are
this paper; what is still missing is threading a per-step tolerance through
`reachOrders`'s own induction.

The count is low and the list below is long because the work here follows the
paper's *approach* without proving any of its numbered results. That reading has
now been done: every one of the nineteen files that cite the paper was read
against it, and not one states a result below. 🔴 0/12 is confirmed rather than
merely unexamined, and the findings say what stands in the way of the rest.

## Results

| Result | What it says | In CORALean |
|---|---|---|
| `Prop. 1` | Bounds the Hausdorff distance between a set S= and its Minkowski sum S_tot = S= ⊕ S+ (0 ∈ S+) by err(S+) := r(box(S+)), the enclosing radius of the box over-approximation of S+. | — |
| `Assumption 1` | (Convergence of ε_H and ε_P) Floating-point errors are neglected so that ε_H([t_i,t_{i+1}]) → 0 and ε_P([t_i,t_{i+1}]) → 0 as Δt_i → 0. | — |
| `Def. 1` | (Superlinear decrease) A continuous function f's set-based evaluation f(S(t)) decreases superlinearly if for all φ∈(0,1), f(S([t,t+φΔt])) ⊆ φ·f(S([t,t+Δt])). | — |
| `Prop. 2` | If ε_P([t_i,t_{i+1}]) decreases superlinearly (Def. 1), then for any ε_{P,max} > 0 there exists a sequence of time intervals such that the sum of the errors stays below ε_{P,max}. | — |
| `Thm. 1` | Alg. 1 (fully automated parameter tuning) terminates and keeps the overall error below a user-defined bound ε_max, assuming the set-representation-size reduction step in each iteration is optional. | — |
| `Alg. 1` | "Fully automated parameter tuning": given ε_{H,max}, ε_{P,max}, ε_{S,max}, t_f, iteratively computes Δt_i, calls Alg. 2 and Alg. 3 to tune the time step and set representation size, and returns the reachable set R([0,t_f]). | — |
| `Alg. 2` | "Adapt values for Δt, Φ_prop": computes the time step size Δt_i and the proportional error budget Φ_prop,i for the current step, given the running error ε_P([0,t_i]). | — |
| `Alg. 3` | "Adapt values for Φ_set": adapts the target zonotope order/set-representation-size parameter Φ_set by decreasing the number of generators of the particular-solution reachable set. | — |
| `Prop. 3` | The error ε_H([t_i,t_{i+1}]) (linearization-error-enclosure error, eq. (21)) converges to 0 as Δt_i → 0, and therefore satisfies Assumption 1. | — |
| `Prop. 4` | The error ε_P([t_i,t_{i+1}]) (particular-solution error, eq. (22)) converges to 0 as Δt_i → 0, and therefore satisfies Assumption 1. | — |
| `Lemma 1` | The size of the matrix-exponential remainder E(Δt,η) decreases superlinearly with respect to Δt: for all φ∈(0,1), E(φΔt,η) ⊆ φ·E(Δt,η). | — |
| `Thm. 2` | The error ε_P([t_i,t_{i+1}]) (eq. (22)) decreases superlinearly according to Def. 1: for all φ∈(0,1), ε_P([t_i,t_i+φΔt_i]) ≤ φ·ε_P([t_i,t_i+Δt_i]). | — |
| `Def. 2` | (Zonotopes) [cites [27, Def. 1]] Z = {x∈R^n \| x = c + Σ_{i=1}^γ β_i g^(i), -1≤β_i≤1} with center c and generators g^(1),...,g^(γ); the order is ρ = γ/n. | n/a — restated from Girard 2005, which this formalization does not draw on directly |

## Findings

**`Prop. 1`, and everything the paper budgets with it, is at a norm this
formalization does not carry.** The quantity is `err(S) := r(box(S))`, and
`Prop. 1` defines `r(·)` as returning "the radius of the smallest hypersphere
centered at the origin enclosing its argument" — Euclidean by construction, not
incidentally. `Vec ℝ n` is `Fin n → ℝ` and carries Mathlib's *supremum* norm;
`‖·‖₂` is spelt out separately in `Global/EuclideanNorm.lean` and deliberately
not wired into a metric instance, so `Metric.closedBall` and
`Metric.hausdorffDist` read the sup norm there. `Assumption 1`, `Prop. 2`,
`Prop. 3`, `Prop. 4` and `Thm. 2` are stated in terms of ε_H and ε_P, which are
`err(·)` values, and inherit it. This is the same gap that holds NAHS'22
`Thm. 1` and TAC'23 `Prop. 1`-`Prop. 4` open — a limitation of ours, not a
defect of the paper. Two theorems in the tree have `Prop. 1`'s exact shape, an
image inside a base widened by a ball, and are still not it: the balls are
sup-norm, and the radius is `(∑ⱼ absBound j)` scaled by a series remainder
rather than the Euclidean radius of a box.
[`TimeIntervalStepSubsetInitialAddError.lean`](../../src/CORALean/ContDynamics/LinearSys/Theorems/TimeIntervalStepSubsetInitialAddError.lean),
[`TimePointStepSubsetConstInputAddError.lean`](../../src/CORALean/ContDynamics/LinearSys/Theorems/TimePointStepSubsetConstInputAddError.lean)

**`Lemma 1` is the row the norm does not block.** Its subject E(Δt, η) is an
entrywise interval matrix and its claim E(φΔt, η) ⊆ φ·E(Δt, η) a set inclusion,
with no norm in it anywhere. What is missing is the object: `expRemainderBound`
bounds the same remainder with a single scalar under the `l∞` operator norm,
and a scalar bound is not the entrywise matrix. The geometric-series argument
behind `MatExp.tendsto_expRemainderBound_atTop` should carry over entrywise once
that matrix is defined — the same conclusion the
[TAC 2023 page](../2023/wetzlinger-fully-automated-verification.md) reached
about its own `Lemma 1`.
[`Enclosures.lean`](../../src/CORALean/ContDynamics/LinearSys/MatExp/Enclosures.lean)

## Cited without a result

These name the paper as a whole. A locator would put each in a row above.

* [`ExpRemainderOrder.lean`](../../src/CORALean/ContDynamics/LinearSys/MatExp/ExpRemainderOrder.lean)
* [`ExpRemainderStep.lean`](../../src/CORALean/ContDynamics/LinearSys/MatExp/ExpRemainderStep.lean)
* [`ExistsExpRemainderBoundLt.lean`](../../src/CORALean/ContDynamics/LinearSys/MatExp/Theorems/ExistsExpRemainderBoundLt.lean)
* [`ExistsMulExpRemainderBoundLt.lean`](../../src/CORALean/ContDynamics/LinearSys/MatExp/Theorems/ExistsMulExpRemainderBoundLt.lean)
* [`TendstoExpRemainderBoundAtTop.lean`](../../src/CORALean/ContDynamics/LinearSys/MatExp/Theorems/TendstoExpRemainderBoundAtTop.lean)
* [`TendstoMulExpRemainderBoundZero.lean`](../../src/CORALean/ContDynamics/LinearSys/MatExp/Theorems/TendstoMulExpRemainderBoundZero.lean)
* [`TimeIntervalStepEps.lean`](../../src/CORALean/ContDynamics/LinearSys/Operations/TimeIntervalStepEps.lean)
* [`StepError.lean`](../../src/CORALean/ContDynamics/LinearSys/StepError.lean)
* [`ExistsTimeIntervalStepErrorLt.lean`](../../src/CORALean/ContDynamics/LinearSys/Theorems/ExistsTimeIntervalStepErrorLt.lean)
* [`ExistsTimePointStepErrorLt.lean`](../../src/CORALean/ContDynamics/LinearSys/Theorems/ExistsTimePointStepErrorLt.lean)
* [`TimeIntervalStepSubsetInitialAddError.lean`](../../src/CORALean/ContDynamics/LinearSys/Theorems/TimeIntervalStepSubsetInitialAddError.lean)
* [`TimePointStepSubsetConstInputAddError.lean`](../../src/CORALean/ContDynamics/LinearSys/Theorems/TimePointStepSubsetConstInputAddError.lean)
* [`Operations.lean`](../../src/CORALean/ContDynamics/LinearSysDT/Operations.lean)
* [`ReachOrdersStepSubsetClosedBallOfReduceBoxOrder.lean`](../../src/CORALean/ContDynamics/LinearSysDT/Theorems/ReachOrdersStepSubsetClosedBallOfReduceBoxOrder.lean)
* [`ReachSubsetClosedBall.lean`](../../src/CORALean/ContDynamics/LinearSysDT/Theorems/ReachSubsetClosedBall.lean)
* [`ReduceBoxOrder.lean`](../../src/CORALean/ContSet/Zonotope/Real/ReduceBoxOrder.lean)
* [`ReduceBoxAntitone.lean`](../../src/CORALean/ContSet/Zonotope/Real/Theorems/ReduceBoxAntitone.lean)
* [`ReduceBoxEqOfPoint.lean`](../../src/CORALean/ContSet/Zonotope/Real/Theorems/ReduceBoxEqOfPoint.lean)
* [`StepSubsetClosedBallOfReduceBoxOrder.lean`](../../src/CORALean/ContSet/Zonotope/Real/Theorems/StepSubsetClosedBallOfReduceBoxOrder.lean)
