# Adaptive parameter tuning for reachability analysis of linear systems

```bibtex
@inproceedings{wetzlinger2020adaptive,
  author = {Wetzlinger, M. and Kochdumper, N. and Althoff, M.},
  title = {Adaptive parameter tuning for reachability analysis of linear systems},
  booktitle = {2020 59th IEEE Conference on Decision and Control (CDC)},
  year = {2020}
}
```

**Source:** https://arxiv.org/pdf/2006.12091 — the arXiv preprint of the CDC paper, read with `pypdf` (poppler is not installed here, so the Read tool's PDF-page mode is unavailable). The table was seeded from https://ar5iv.labs.arxiv.org/html/2006.12091, whose numbering is not to be trusted; every locator below has since been re-read off the PDF and none of them moved.  
**Inventory:** confirmed

Every tuning knob a reachability run has — the time step, the order a set is
reduced to, how the error budget is split — chosen against a stated tolerance
instead of guessed. `reduceBoxOrder`, the step selectors and `reachOrders` are
this paper; what is still missing is threading a per-step tolerance through
`reachOrders`'s own induction.

The count was 🔴 0/12 because the older work here follows the paper's
*approach* without proving any of its numbered results — every one of the
nineteen files that cited the paper was read against it, and not one stated a
result. `Prop. 1`, `Def. 1` and `Lemma 1` landed first: a generic
Hausdorff-distance bound, a predicate over any real vector space, and a fact
about the matrix-exponential remainder already in the tree. `Assumption 1`,
`Prop. 2`, `Prop. 3`, `Prop. 4` and `Thm. 2` — the convergence block sitting on
top of them — landed next, then the three algorithms and `Thm. 1`. Every row in
scope now points at a file, and six findings say where the printed result had to
be departed from: two loop conditions with the wrong connective, a proposition
that does not follow from the definition it cites, a missing termination bound,
and `Thm. 1`'s termination half, which is not established here.

## Results

| Result | What it says | In CORALean | Class |
|---|---|---|---|
| `Prop. 1` | Bounds the Hausdorff distance between a set S= and its Minkowski sum S_tot = S= ⊕ S+ (0 ∈ S+) by err(S+) := r(box(S+)), the enclosing radius of the box over-approximation of S+. | [`HausdorffDist2AddLeBoxRadius.lean`](../../src/CORALean/ContSet/Interval/Real/Theorems/HausdorffDist2AddLeBoxRadius.lean) | `correct` |
| `Assumption 1` | (Convergence of ε_H and ε_P) Floating-point errors are neglected so that ε_H([t_i,t_{i+1}]) → 0 and ε_P([t_i,t_{i+1}]) → 0 for Δt_i → 0. | [`IsErrorConvergingToZero.lean`](../../src/CORALean/Global/IsErrorConvergingToZero.lean) — the predicate, one step-error function of Δt at a time; `Prop. 3` and `Prop. 4` below discharge it for eq. (21)'s ε_H and eq. (22)'s ε_P themselves | `correct` |
| `Def. 1` | (Superlinear decrease) A continuous function f's set-based evaluation f(S(t)) decreases superlinearly if for all φ∈(0,1), f(S([t,t+φΔt])) ⊆ φ·f(S([t,t+Δt])). | [`HasSuperlinearDecrease.lean`](../../src/CORALean/Global/HasSuperlinearDecrease.lean) | `correct` |
| `Prop. 2` | If ε_P(Δt)/Δt → 0 as Δt → 0 — what [1]'s "decreases superlinearly (Def. 1)" has to mean for its own claim to hold, see Findings — then for any ε_{P,max} > 0 and any horizon t_f > 0 there is a finite partition of [0,t_f] whose ε_P-errors sum below ε_{P,max}. | [`HorizonErrorBudget.lean`](../../src/CORALean/Global/HorizonErrorBudget.lean); [`HorizonErrorBudget.lean`](../../src/CORALean/Global/Counterexamples/HorizonErrorBudget.lean) — the linear `ε_P(Δt) = Δt` meets Def. 1 and no partition of `[0, 2]` keeps its errors below `1` **Counterexample:** `exists_finPartition_sum_particularError_le_counterexample` | `fixed` — needs `ε_P(Δt)/Δt → 0`, which Def. 1 does not give (a linear `ε_P` satisfies it); formalized with that hypothesis |
| `Thm. 1` | Alg. 1 (fully automated parameter tuning) terminates and keeps the overall error below a user-defined bound ε_max, assuming the set-representation-size reduction step in each iteration is optional. | the *error* half, outright: [`TunedRunErrorBudget.lean`](../../src/CORALean/ContDynamics/LinearSys/Theorems/TunedRunErrorBudget.lean) — a run that does not step past t_f keeps ε_P([0,t_i]) ≤ ε_{P,max}, ε_S([0,t_i]) ≤ ε_{S,max} and the last step's ε_H ≤ ε_{H,max}, so the budgeted total stays under ε_max = ε_{H,max}+ε_{P,max}+ε_{S,max}. The *termination* half is not established — see the Findings | `proof-gap` — termination argument does not follow (steps may shrink geometrically); the error half is proved for runs that stay within `t_f` |
| `Alg. 1` | "Fully automated parameter tuning": given ε_{H,max}, ε_{P,max}, ε_{S,max}, t_f, iteratively computes Δt_i, calls Alg. 2 and Alg. 3 to tune the time step and set representation size, and returns the reachable set R([0,t_f]). | (lines 5-10), [`TunedRun.lean`](../../src/CORALean/ContDynamics/LinearSys/Operations/TunedRun.lean) (the loop of lines 4-11) and [`TunedReach.lean`](../../src/CORALean/ContDynamics/LinearSys/Operations/TunedReach.lean) (line 12); line 6's `HR` is `timeInterval`, without eq. (19)'s `Fu(Δt,η)c_u` term; the error budget it keeps is `Thm. 1`'s row. In floats, [`ReachAdaptiveFloat.lean`](../../src/CORALean/ContDynamics/LinearSys/Operations/ReachAdaptiveFloat.lean) runs it ([`AdaptiveStepFloat.lean`](../../src/CORALean/ContDynamics/LinearSys/Operations/AdaptiveStepFloat.lean) lines 5-10, [`AdaptiveRunFloat.lean`](../../src/CORALean/ContDynamics/LinearSys/Operations/AdaptiveRunFloat.lean) the loop), clipping `Δt_i` to `t_f − t_i` as CORA's `maxTimeStep` does, and [`ReachAdaptiveFloatOuter.lean`](../../src/CORALean/ContDynamics/LinearSys/Theorems/ReachAdaptiveFloatOuter.lean) is its soundness — the windows cover `[t_0, t_f]` and hold every run, whatever the tuning chose; it is an outer theorem, not `Thm. 1`'s error half | `underspecified` — nothing clips `Δtᵢ` to `t_f − tᵢ` |
| `Alg. 2` | "Adapt values for Δt, Φ_prop": picks the step size Δt_i and the propagation parameters Φ_prop,i — the truncation order η at [1]'s own implementation, not an error budget — for the current step, given the running error ε_P([0,t_i]). | [`AdaptTimeStep.lean`](../../src/CORALean/ContDynamics/LinearSys/Operations/AdaptTimeStep.lean), held to line 12's two bounds by [`AdaptTimeStepBudget.lean`](../../src/CORALean/ContDynamics/LinearSys/Theorems/AdaptTimeStepBudget.lean) and shown to succeed at some fuel by [`ExistsAdaptTimeStepFuel.lean`](../../src/CORALean/ContDynamics/LinearSys/Theorems/ExistsAdaptTimeStepFuel.lean); line 12's printed connective and the step sweep's missing iteration bound are in the Findings; in floats, [`AdaptTimeStepFloat.lean`](../../src/CORALean/ContDynamics/LinearSys/Operations/AdaptTimeStepFloat.lean), with eq. (21)-(22)'s sets at the float `[e^{At_i}]` and the sup-norm `errOp` for `err`, and without eq. (21)'s `F_u c_u` half | `underspecified` — line 12 has the wrong connective (`∧` for `∨`); the step sweep has no iteration bound |
| `Alg. 3` | "Adapt values for Φ_set": adapts the target zonotope order/set-representation-size parameter Φ_set by decreasing the number of generators of the particular-solution reachable set. | [`AdaptSetOrder.lean`](../../src/CORALean/ContSet/Zonotope/Real/Operations/AdaptSetOrder.lean), held to line 7's bound by [`AdaptSetOrderBudget.lean`](../../src/CORALean/ContSet/Zonotope/Real/Theorems/AdaptSetOrderBudget.lean); line 7's printed connective and which order it leaves the loop holding are in the Findings; in floats, [`AdaptSetOrder.lean`](../../src/CORALean/ContSet/Zonotope/Float/Operations/AdaptSetOrder.lean), keeping the last order that passed as the real layer does | `underspecified` — line 7 has the wrong connective, twice, and returns the order reduced past the budget |
| `Prop. 3` | The error ε_H([t_i,t_{i+1}]) of eq. (21), err(e^{At_i}F_x(Δt_i,η_i)X_0 ⊕ e^{At_i}F_u(Δt_i,η_i)c_u) — the *homogeneous*-solution enclosure's widening term, not a "linearization" error: CDC 2020 is about linear systems — converges to 0 for Δt_i → 0, and therefore satisfies Assumption 1. | [`ErrorConvergesToZeroHomogeneousRemainderError.lean`](../../src/CORALean/ContDynamics/LinearSys/MatExp/Theorems/ErrorConvergesToZeroHomogeneousRemainderError.lean) — of `homogeneousRemainderError`, `err` of eq. (21)'s set itself at every t_i, with F_x and F_u built as eq. (17)-(18) print them over eq. (15)-(16)'s entrywise E; `X_0` bounded, as the zonotope [1] takes it to be. The earlier [`ErrorConvergesToZeroTimeIntervalStepCurvatureError.lean`](../../src/CORALean/ContDynamics/LinearSys/Theorems/ErrorConvergesToZeroTimeIntervalStepCurvatureError.lean) is the same limit for a scalar upper bound of the F_x half at t_i = 0 | `correct` |
| `Prop. 4` | The error ε_P([t_i,t_{i+1}]) of eq. (22), err(e^{At_i}E(Δt_i,η_i)Δt_iU) — the particular-solution enclosure's widening term — converges to 0 for Δt_i → 0, and therefore satisfies Assumption 1. | [`ErrorConvergesToZeroParticularRemainderError.lean`](../../src/CORALean/ContDynamics/LinearSys/MatExp/Theorems/ErrorConvergesToZeroParticularRemainderError.lean) — of `particularRemainderError`, `err` of eq. (22)'s set itself at every t_i, E being eq. (15)-(16)'s; `U` bounded, as the zonotope [1] takes it to be. The earlier [`ErrorConvergesToZeroTimePointStepRemainderError.lean`](../../src/CORALean/ContDynamics/LinearSys/Theorems/ErrorConvergesToZeroTimePointStepRemainderError.lean) is the same limit for a scalar upper bound at t_i = 0 | `correct` |
| `Lemma 1` | The size of the matrix-exponential remainder E(Δt,η) = [−E_abs(Δt,η), E_abs(Δt,η)] of eq. (15)-(16), E_abs(Δt,η) = Σ_{k=η+1}^∞ (\|A\|Δt)^k/k!, decreases superlinearly with respect to Δt: for all φ∈(0,1), E(φΔt,η) ⊆ φ·E(Δt,η). | [`SuperlinearDecreaseExpRemainderMat.lean`](../../src/CORALean/ContDynamics/LinearSys/MatExp/Theorems/SuperlinearDecreaseExpRemainderMat.lean) — of `expRemainderInterval`, eq. (15)-(16)'s entrywise interval matrix, for every step Δt ≥ 0 and with no further condition. [`SuperlinearDecreaseExpRemainder.lean`](../../src/CORALean/ContDynamics/LinearSys/MatExp/Theorems/SuperlinearDecreaseExpRemainder.lean) is the same inclusion for `expRemainder`, the uniform box CORA's operator-norm bound gives, under that bound's side condition ‖Δt·A‖/(η+2) < 1 | `correct` |
| `Thm. 2` | The error ε_P([t_i,t_{i+1}]) of eq. (22) decreases superlinearly according to Def. 1: for all φ∈(0,1), ε_P([t_i,t_i+φΔt_i]) ≤ φ·ε_P([t_i,t_i+Δt_i]). | [`ParticularRemainderErrorSuperlinear.lean`](../../src/CORALean/ContDynamics/LinearSys/MatExp/Theorems/ParticularRemainderErrorSuperlinear.lean) — the displayed inequality for `particularRemainderError`, `err` of eq. (22)'s set itself, at every t_i and every step Δt ≥ 0, through [1]'s own proof: `Lemma 1` gives PR^+(φΔt) ⊆ φ·PR^+(Δt); `U` bounded. The earlier [`SuperlinearDecreaseTimePointStepRemainderError.lean`](../../src/CORALean/ContDynamics/LinearSys/Theorems/SuperlinearDecreaseTimePointStepRemainderError.lean) is the same for a scalar upper bound at t_i = 0, under ‖Δt·A‖/(η+2) < 1 | `correct` |
| `Def. 2` | (Zonotopes) [cites [27, Def. 1]] Z = {x∈R^n \| x = c + Σ_{i=1}^γ β_i g^(i), -1≤β_i≤1} with center c and generators g^(1),...,g^(γ); the order is ρ = γ/n. | n/a — restated from Girard 2005, which this formalization does not draw on directly | `restated` |

## Findings

**`Prop. 1`'s norm obstacle is resolved.** `err(S) := r(box(S))` names a Euclidean radius — `Prop. 1`
defines `r(·)` as "the radius of the smallest hypersphere centered at the origin enclosing its
argument" — and `Vec ℝ n` itself carries Mathlib's *supremum* norm, not that one.
`Global/EuclideanHausdorffDist.lean`'s `hausdorffDist₂`, landed 16-September-2026, is
`Metric.hausdorffDist` taken through `toEuclidean`, so it reads `‖·‖₂` without a metric instance on
`Vec ℝ n` itself, and
[`HausdorffDist2AddLeBoxRadius.lean`](../../src/CORALean/ContSet/Interval/Real/Theorems/HausdorffDist2AddLeBoxRadius.lean)
states and proves `Prop. 1` through it. `Prop. 3`, `Prop. 4` and `Thm. 2` are stated in terms of
`err(·)` values, not distances, and they are now proved of `err` itself — `Global/Err.lean`'s
`r(box(·))`, the same Euclidean radius — at eq. (21)-(22)'s own sets: `Prop. 3` and `Prop. 4` are
what discharge `Assumption 1`, and `Prop. 2` holds of any step error.

**`Prop. 1` — the theorems that share its shape.** NAHS'22 `Thm. 1` and TAC'23 `Prop. 1`-`Prop. 4`
have since taken that route. Two theorems in the tree share `Prop. 1`'s shape, an image inside a
base widened by a ball, and are still not it: the balls are sup-norm, and the radius is
`(∑ⱼ absBound j)` scaled by a series remainder rather than the Euclidean radius of a box.
[`TimeIntervalSubsetInitialAddError.lean`](../../src/CORALean/ContDynamics/LinearSys/Theorems/TimeIntervalSubsetInitialAddError.lean),
[`TimePointStepSubsetConstInputAddError.lean`](../../src/CORALean/ContDynamics/LinearSys/Theorems/TimePointStepSubsetConstInputAddError.lean)

**What ε_H and ε_P actually are.** The page used to gloss ε_H as a "linearization-error-enclosure
error", which cannot be right: CDC 2020 is about *linear* systems, there is no linearization
anywhere in it. Reading eq. (19)-(22) directly:
`HR([0,Δt]) = conv(X₀,e^{AΔt}X₀) ⊕ Fx(Δt,η)X₀ ⊕ Fu(Δt,η)c_u`, with the first (labelled `HR=`) the
exact convex-hull term and the rest (labelled `HR+`) the widening the curvature costs; ε_H :=
err(HR+) is the size of *that widening alone*, not a distance from the hull to any true trajectory.
Symmetrically ε_P := err(PR+) with `PR+ = E(Δt,η)·Δt·U`.

**`ε_H` and `ε_P` — the subterms of the tree's step errors.** `HR+`'s `Fx(Δt,η)X₀` half is
`MatExp.correctionMatrix`'s image under `X₀` — `curv` in `LinearSys.timeInterval`, which carries no
`Fu(Δt,η)c_u` term at all — and `PR+` is `MatExp.inputRemainder`'s image under `U`. Both are proper
*subterms* of this tree's existing `timeIntervalStepError`/`timePointStepError`, which bound a
strictly larger quantity: `timeIntervalStepError` also carries a *hull* term (`‖e^{rA}-I‖`, first
order in the step, independent of η) that measures the hull's own distance from the states the flow
visits, which eq. (21) does not fold into ε_H at all. `timePointStepError` similarly carries a
"dependency" term ε_P does not have.

**`ε_H` and `ε_P` — the scalar bounds and the rows that point past them.**
`timeIntervalStepCurvatureError`/`timePointStepRemainderError` (`StepConvergenceError.lean`) are the
non-hull halves rather than the combined figure the existing `Exists…StepError_lt` theorems bound —
citing those instead would have put a false equivalence on this page. Those two are still not eq.
(21)-(22) themselves: each is a scalar *upper bound* built from `Σⱼ absBound j` and a norm of `A`,
not `err(·) = r(box(·))`, `timeIntervalStepCurvatureError` bounds only the `Fx(Δt,η)X₀` half of
`HR+`, and both sit at the base step `[0,r]`. The rows now point past them, at
[`HomogeneousRemainderError.lean`](../../src/CORALean/ContDynamics/LinearSys/MatExp/Definitions/HomogeneousRemainderError.lean)
and
[`ParticularRemainderError.lean`](../../src/CORALean/ContDynamics/LinearSys/MatExp/Definitions/ParticularRemainderError.lean):
`err` of eq. (21)'s and eq. (22)'s sets at every `t_i`, the `e^{At_i}` pre-multiplication included,
with `F_x`, `F_u` and `E` built as eq. (15)-(18) print them — `E` entrywise at `|A|`, not
`correctionMatrix`'s uniform box.

**`Prop. 2` needs more than `Def. 1` gives.** [1]'s own proof of `Prop. 2`
treats "ε_P decreases superlinearly" as if it forced ε_P(Δt)/Δt → 0, but
`HasSuperlinearDecrease` read at one reference length Δt only bounds ε_P(Δt) by
the *line through* `(Δt_ref,ε_P(Δt_ref))` — a linear ε_P (equality
throughout) satisfies Def. 1 exactly, and for it ε_P(Δt)/Δt is a fixed
positive constant that no ε_{P,max} budget could beat. `HorizonErrorBudget.lean`
proves the proposition from the hypothesis that actually makes it true,
ε_P(Δt)/Δt → 0, and does so for eq. (22)'s own ε_P too: since
`expRemainderBound` is `O(Δt^{η+1})` near `0`, `timePointStepRemainderError`
is `O(Δt^{η+2})` and its ratio to Δt genuinely vanishes. The theorem proved
is the horizon-covering reading — a finite partition of a *fixed* `[0,t_f]`
— not the strictly weaker "some sequence exists, of whatever total length",
which `Assumption 1` already gives for free and which `Thm. 1` could not use.

**Both printed loop conditions have the wrong connective, and `Alg. 3`'s is wrong twice.** `Alg. 2`
line 12 is `while ε_H > ε_H,max ∧ ε_P > ε_P,max,i`: a do-while repeating while *that* holds leaves
as soon as *either* error is met, so a step clearing ε_H alone is accepted with its ε_P unbounded.
`Thm. 1`'s own proof asks for both — "∀i : ε_P([t_i,t_{i+1}]) ≤ ε_P,max,i , ε_H([t_i,t_{i+1}]) ≤
ε_H,max" — and the negation of that exit condition is the *disjunction*, which is what
[`AdaptTimeStep.lean`](../../src/CORALean/ContDynamics/LinearSys/Operations/AdaptTimeStep.lean)
writes.

**`Alg. 3` — line 7 and the order of the steps.** `Alg. 3` line 7 is
`while ε_S < ε_S,max,i ∨ decr(Φ_set) = Φ_set`, whose second disjunct says a further decrement is
*impossible*: as printed the loop never leaves once the order bottoms out. `Thm. 1` again says the
loop exits when either the bound is exceeded or the parameters "have been reduced as much as
possible", so that `∨` is an `∧` and its second conjunct `decr(Φ_set) ≠ Φ_set`: flipping the
connective alone still never leaves once the order bottoms out. Beyond the connective, lines 4-6
decrement, reduce and *then* measure, and line 7 exits on the measurement failing — so the
`PR([0,t_{i+1}])` line 8 hands back is the one reduced past the budget, and the ε_S it accumulates
exceeds the share eq. (13) allows.
[`AdaptSetOrder.lean`](../../src/CORALean/ContSet/Zonotope/Real/Operations/AdaptSetOrder.lean) keeps
the last order that passed, which is what makes `adaptSetOrder_budget` true at all.

**`Alg. 2`'s step sweep has no termination bound in [1]; `Alg. 3`'s loop needs none.** `Alg. 2`
shrinks Δt_i by μ and restarts, and `Thm. 1` argues termination from `Prop. 2` without an iteration
count following from it, so the definition carries an explicit `fuel` and returns `none` where it
runs out — never a step it did not check.
[`ExistsAdaptTimeStepFuel.lean`](../../src/CORALean/ContDynamics/LinearSys/Theorems/ExistsAdaptTimeStepFuel.lean)
supplies the missing half at the coarsest order: for 0 < μ < 1, a positive ε_H,max and a positive
remaining share, some fuel suffices, because ε_H → 0 (`Prop. 3`) while ε_P's cofactor past the Δt_i
it carries → 0 against a share that is merely *linear* in Δt_i. That is the asymmetry `Prop. 2`
turns on, here at one geometric sequence rather than over a partition. The order sweep is bounded by
[1]'s own Φ_prop,max, and `Alg. 3` by the set's own generator count: `Z.h` decrements reach every
order there is.

**The comparison is an argument, not a classical decision.** Both subroutines
take `le : ℝ → ℝ → Bool` and put every decision through it, so each search is a
bounded structural recursion rather than a `Nat.find`, and a float layer
transcribes it with `FloatOps.le` and runs it; they are `noncomputable` only
because ℝ arithmetic is. Soundness asks `le a b = true → a ≤ b` alone, so a
check that gives up early loses candidates and never reports a wrong one; the
existence half asks the converse instead. This is deliberately *not* the shape
of `MatExp.expRemainderOrder`, `MatExp.expRemainderStep` and
`Zonotope.reduceBoxOrder` — the three knobs of this same paper already in the
tree, all three `Nat.find` or `Classical.choose` under classical decidability,
and none of them runnable.

**`Thm. 1` is two claims, and only the error one closes.** [1]'s proof of `Thm. 1` runs termination
first and the bound second, and the two do not lean on each other.

**`Thm. 1` — termination.** *Termination. Three loops. `Alg. 3`'s is bounded by the set's own
generator count, as above. `Alg. 2`'s is not, and `Alg. 1` inherits that through the `Option`
[`TunedRun.lean`](../../src/CORALean/ContDynamics/LinearSys/Operations/TunedRun.lean) returns. The
main loop's own argument — "the time `t` monotonically increases (line 10), eventually reaching
`t_f`" — does not follow: `Alg. 2` shrinks `Δt_i` by `μ` with no positive lower bound, and a
monotonically increasing `t` whose increments shrink geometrically need not reach `t_f` at all.
`Prop. 2` exhibits *a* partition of `[0,t_f]`, but nothing shows `Alg. 1`'s greedy choices are one,
and `Prop. 2` as printed is itself the gap recorded above. So no termination is claimed here.

**`Thm. 1` — the bound.** *The bound. It is about the budgeted error terms, not about a Hausdorff
distance from `R_ex`: `Prop. 1` relates each `err(·)` to the distance one summand costs, and nothing
in [1] composes the three into a distance from the exact reachable set — reading `Thm. 1` as the
latter would be the false claim. What [1] then proves is weaker still: that each of `ε_{H,max}`,
`ε_{P,max}`, `ε_{S,max}` is *satisfiable*, not that a run of `Alg. 1` stays inside them.
[`TunedRunErrorBudget.lean`](../../src/CORALean/ContDynamics/LinearSys/Theorems/TunedRunErrorBudget.lean)
proves the accumulation does, by eq. (10)/(11)'s telescoping: a share of what is left of the budget,
proportional to the step, keeps `ε_P([0,t_i])` under `ε_{P,max}·t_i/t_f`, and the same for `ε_S`.

**`Thm. 1` — the optimal reduction.** [1]'s hypothesis "assuming the reduction of the set
representation in each step is optional" is what makes `ε_{S,max}` satisfiable at all — reduce
nothing and `ε_S([t_i,t_{i+1}]) = 0`, the remark under eq. (13) — and it is discharged rather than
assumed: `Alg. 3` starts at `param(PR)`, which drops no generator. One side condition is left
standing, and it is [1]'s omission rather than the theorem's: nothing in `Alg. 1` clips `Δt_i` to
`t_f - t_i`, and eq. (10)'s share is only a share while it is clipped, so the theorem asks that the
run does not step past the horizon.

**The float run proves soundness, not `ε_max`.** `reachAdaptiveFloat_outer`
holds whatever `Alg. 2` and `Alg. 3` chose, and no theorem bounds the distance
from its windows to the exact reachable set. Four things stand between the
tuned errors and such a bound, besides `Thm. 1`'s own gap above: eq. (21)'s
`ε_H` leaves out the hull `conv(X₀, e^{AΔt}X₀)`'s distance from the flow, first
order in `Δt` (`timeIntervalStepError`'s hull term). The constant input rides
on `P̃^R([0,ũ])`, also first order, since the float layer has no `F_u`; the
float `[e^{At_i}]` and every interval-matrix product add a box no `ε` counts;
and `errOp` is the sup-norm radius of a box, where eq. (21)-(22) take the
Euclidean `r(box(·))`.

## Cited without a result

These name the paper as a whole. A locator would put each in a row above.

* [`TimeIntervalStepCurvatureError.lean`](../../src/CORALean/ContDynamics/LinearSys/Operations/TimeIntervalStepCurvatureError.lean)
* [`AdaptTimeStepOrder.lean`](../../src/CORALean/ContDynamics/LinearSys/Operations/AdaptTimeStepOrder.lean)
* [`AdaptTimeStepSearch.lean`](../../src/CORALean/ContDynamics/LinearSys/Operations/AdaptTimeStepSearch.lean)
* [`TimePointStepRemainderError.lean`](../../src/CORALean/ContDynamics/LinearSys/Operations/TimePointStepRemainderError.lean)
* [`ExpRemainderOrder.lean`](../../src/CORALean/ContDynamics/LinearSys/MatExp/Operations/ExpRemainderOrder.lean)
* [`ExpRemainderStep.lean`](../../src/CORALean/ContDynamics/LinearSys/MatExp/Operations/ExpRemainderStep.lean)
* [`OrderTestFloat.lean`](../../src/CORALean/ContDynamics/LinearSys/MatExp/Operations/OrderTestFloat.lean)
* [`StepTestFloat.lean`](../../src/CORALean/ContDynamics/LinearSys/MatExp/Operations/StepTestFloat.lean)
* [`TuneOrderFloat.lean`](../../src/CORALean/ContDynamics/LinearSys/MatExp/Operations/TuneOrderFloat.lean)
* [`TuneStepFloat.lean`](../../src/CORALean/ContDynamics/LinearSys/MatExp/Operations/TuneStepFloat.lean)
* [`SideConditionOfLeFloat.lean`](../../src/CORALean/ContDynamics/LinearSys/MatExp/Theorems/SideConditionOfLeFloat.lean)
* [`StepTestSpecFloat.lean`](../../src/CORALean/ContDynamics/LinearSys/MatExp/Theorems/StepTestSpecFloat.lean)
* [`TuneOrderIsSomeFloat.lean`](../../src/CORALean/ContDynamics/LinearSys/MatExp/Theorems/TuneOrderIsSomeFloat.lean)
* [`TuneOrderSpecFloat.lean`](../../src/CORALean/ContDynamics/LinearSys/MatExp/Theorems/TuneOrderSpecFloat.lean)
* [`TuneStepIsSomeFloat.lean`](../../src/CORALean/ContDynamics/LinearSys/MatExp/Theorems/TuneStepIsSomeFloat.lean)
* [`TuneStepSpecFloat.lean`](../../src/CORALean/ContDynamics/LinearSys/MatExp/Theorems/TuneStepSpecFloat.lean)
* [`TimeIntervalTunedOuter.lean`](../../src/CORALean/ContDynamics/LinearSys/Theorems/TimeIntervalTunedOuter.lean)
* [`ExistsExpRemainderBoundLt.lean`](../../src/CORALean/ContDynamics/LinearSys/MatExp/Theorems/ExistsExpRemainderBoundLt.lean)
* [`ExistsMulExpRemainderBoundLt.lean`](../../src/CORALean/ContDynamics/LinearSys/MatExp/Theorems/ExistsMulExpRemainderBoundLt.lean)
* [`TendstoExpRemainderBoundAtTop.lean`](../../src/CORALean/ContDynamics/LinearSys/MatExp/Theorems/TendstoExpRemainderBoundAtTop.lean)
* [`TendstoMulExpRemainderBoundZero.lean`](../../src/CORALean/ContDynamics/LinearSys/MatExp/Theorems/TendstoMulExpRemainderBoundZero.lean)
* [`TimeIntervalStepEps.lean`](../../src/CORALean/ContDynamics/LinearSys/Operations/TimeIntervalStepEps.lean)
* [`TimePointStepError.lean`](../../src/CORALean/ContDynamics/LinearSys/Operations/TimePointStepError.lean)
* [`TimeIntervalStepError.lean`](../../src/CORALean/ContDynamics/LinearSys/Operations/TimeIntervalStepError.lean)
* [`ExistsTimeIntervalStepErrorLt.lean`](../../src/CORALean/ContDynamics/LinearSys/Theorems/ExistsTimeIntervalStepErrorLt.lean)
* [`ExistsTimePointStepErrorLt.lean`](../../src/CORALean/ContDynamics/LinearSys/Theorems/ExistsTimePointStepErrorLt.lean)
* [`IsOrderAdmissible.lean`](../../src/CORALean/ContDynamics/LinearSys/MatExp/Definitions/IsOrderAdmissible.lean)
* [`IsStepAdmissible.lean`](../../src/CORALean/ContDynamics/LinearSys/MatExp/Definitions/IsStepAdmissible.lean)
* [`IsBoundedParticularRemainderSet.lean`](../../src/CORALean/ContDynamics/LinearSys/MatExp/Theorems/IsBoundedParticularRemainderSet.lean)
* [`NormLeOfMemParticularRemainderSet.lean`](../../src/CORALean/ContDynamics/LinearSys/MatExp/Theorems/NormLeOfMemParticularRemainderSet.lean)
* [`AbsEntryLeOfMemStateCorrectionSet.lean`](../../src/CORALean/ContDynamics/LinearSys/MatExp/Theorems/AbsEntryLeOfMemStateCorrectionSet.lean)
* [`AbsEntryLeOfMemInputCorrectionSet.lean`](../../src/CORALean/ContDynamics/LinearSys/MatExp/Theorems/AbsEntryLeOfMemInputCorrectionSet.lean)
* [`TimeIntervalSubsetInitialAddError.lean`](../../src/CORALean/ContDynamics/LinearSys/Theorems/TimeIntervalSubsetInitialAddError.lean)
* [`TimePointStepSubsetConstInputAddError.lean`](../../src/CORALean/ContDynamics/LinearSys/Theorems/TimePointStepSubsetConstInputAddError.lean)
* [`ReachOrders.lean`](../../src/CORALean/ContDynamics/LinearSysDT/Operations/ReachOrders.lean)
* [`ReachOrdersStepClosedBallOfReduceBoxOrder.lean`](../../src/CORALean/ContDynamics/LinearSysDT/Theorems/Real/ReachOrdersStepClosedBallOfReduceBoxOrder.lean)
* [`ReachSubsetClosedBall.lean`](../../src/CORALean/ContDynamics/LinearSysDT/Theorems/Real/ReachSubsetClosedBall.lean)
* [`ReduceBoxOrder.lean`](../../src/CORALean/ContSet/Zonotope/Real/Operations/ReduceBoxOrder.lean)
* [`ErrOp.lean`](../../src/CORALean/ContSet/Zonotope/Float/Operations/ErrOp.lean)
* [`IsReduceBoxAdmissible.lean`](../../src/CORALean/ContSet/Zonotope/Real/Definitions/IsReduceBoxAdmissible.lean)
* [`AdaptSetOrderLoop.lean`](../../src/CORALean/ContSet/Zonotope/Real/Operations/AdaptSetOrderLoop.lean)
* [`ReduceBoxAntitone.lean`](../../src/CORALean/ContSet/Zonotope/Real/Theorems/ReduceBoxAntitone.lean)
* [`ReduceBoxEqOfPoint.lean`](../../src/CORALean/ContSet/Zonotope/Real/Theorems/ReduceBoxEqOfPoint.lean)
* [`StepSubsetClosedBallOfReduceBoxOrder.lean`](../../src/CORALean/ContSet/Zonotope/Real/Theorems/StepSubsetClosedBallOfReduceBoxOrder.lean)
