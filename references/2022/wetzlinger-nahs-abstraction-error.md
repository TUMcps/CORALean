# Adaptive Reachability Algorithms for Nonlinear Systems Using Abstraction Error Analysis

M. Wetzlinger, A. Kulmburg, A. Le Penven and M. Althoff. "Adaptive Reachability Algorithms
for Nonlinear Systems Using Abstraction Error Analysis". Nonlinear Analysis: Hybrid
Systems, vol. 46, 2022, p. 101252.

**Source:** https://mediatum.ub.tum.de/doc/1725668/document.pdf — Wetzlinger's thesis, Appendix A.6 (pp. 121–150), a verbatim reprint of the Elsevier version, read with `pypdf` (poppler is not installed here, so the Read tool's PDF-page mode is unavailable, and the journal version at https://doi.org/10.1016/j.nahs.2022.101252 is paywalled; the paper has no arXiv preprint).  
**Inventory:** confirmed

What a time step size can and cannot buy for a nonlinear system. The gain function
measures how the local abstraction error shrinks when the step does, `Thm. 2` says
that ratio converges to δ^{q+1} for the gain order q, and for most nonlinear systems
q comes out 0 — the error shrinks only linearly in the step size, so the wrapping
effect cannot be tuned away, only paid for. Beside the main result it carries the zonotope-order-reduction bounds
the adaptive algorithms use: `Thm. 1`'s ω_max is the bound the
[HSCC 2021 paper](../2021/wetzlinger-hscc-adaptive-tuning-nonlinear.md) proved as its
`Thm. 3.2`, joined here by ω_rad and ω_cut. `Lemma 1` and all three bounds are
proved, the first over any normed space and the other three at `‖·‖₂`, the norm
the paper states them in. `ReduceBoxOrder` and `ReduceBoxAntitone` are
where a chosen reduction order would be held against one of these bounds, and
the tree still cites the CDC 2020 paper there.

`Def. 4`'s two error measures, `Def. 5`'s gain function and `Def. 6`'s gain order
are formalized, all three over one `d(box(·))` on a bare set: the sets they measure
are a Minkowski difference and an infinite Minkowski sum, and neither is a
representation with an `Interval.radius` to double. `Prop. 1` is what holds that
infinite sum against the paper, and it is an exact equality rather than an
enclosure: each summand's maximum over Ψ(h) is attained at a sign pattern of the
generators and the summands' choices are independent, so the series of row norms is
reached and not merely bounded. Its two ingredients are `Zonotope.supportBound`,
attained, and summability of Σ_p h^{p+1}/(p+1)!·‖A(h)‖^p at the l-infinity operator
norm, which asks nothing of A — the exponential series dominates it termwise.

`Lemma 3`, `Thm. 2` and `Prop. 2` are what that expansion is for, and two of the
three carry a hypothesis the paper does not print: `Lemma 3`'s dichotomy needs f
analytic and not merely smooth, and `Thm. 2`'s limit needs the expansion already
in factored form, which is the one step of its proof that passes to the limit
inside an infinite series. `Prop. 2`'s (42) needs neither — with the Q^(p)_i held
constant the bound φ_i ≤ δ^{q_i+1} falls out of (35) one term at a time — and its
(41) is false as printed: its proof drops the derivatives of the Q^(p)_i, and the
limit is `δ^{q_i+1}(δ − 1) g'(0)/g(0)`, positive when the width loses relative size to its
leading term.

## Results

| Result | What it says | In CORALean | Class |
|---|---|---|---|
| `Def. 1` | (Zonotopes) [cites [26, Def. 1]] Z := {x \| x = c + Σ_{i=1}^γ α_i g^(i), -1≤α_i≤1}, with order ρ := γ/n and shorthand ⟨c,G⟩_Z. | n/a — restated from Girard 2005, which this formalization does not draw on directly | `restated` |
| `Def. 2` | (Hausdorff Distance) For compact V,W⊂R^n, d_H(V,W) := max{d^(1)_H(V,W), d^(2)_H(V,W)} with d^(1)_H(V,W) := max_{v∈V} min_{w∈W} ‖v-w‖_2 and d^(2)_H symmetrically. | n/a — Mathlib's `Metric.hausdorffDist` provides it, used in [`HausdorffDistAddLe.lean`](../../src/CORALean/ContSet/ContSet/Theorems/HausdorffDistAddLe.lean) and [`HausdorffDistIntervalLe.lean`](../../src/CORALean/ContSet/Zonotope/Real/Theorems/HausdorffDistIntervalLe.lean). Mathlib's is the distance of whatever metric the ambient type carries, which at `Vec ℝ n` is the supremum norm and not this definition's ‖·‖_2; [`EuclideanHausdorffDist.lean`](../../src/CORALean/Global/EuclideanHausdorffDist.lean) takes it through `toEuclidean` instead, and that composite is this definition exactly | `mathlib` |
| `Lemma 1` | For compact S,V,W⊂R^n: d_H(S⊕V, S⊕W) ≤ d_H(V,W) — which is what lets order reduction be analyzed on the reduced part Z alone, since d_H(Z_full,Z_red) = d_H(Z'⊕Z, Z'⊕box(Z)) ≤ d_H(Z,box(Z)). | [`HausdorffDistAddLe.lean`](../../src/CORALean/ContSet/ContSet/Theorems/HausdorffDistAddLe.lean) — over any normed space, and on the exact Minkowski sum; `V` and `W` carry the compactness and nonemptiness Mathlib's real-valued distance needs to be the distance and not its junk value | `correct` |
| `Thm. 1` | For a zonotope Z=⟨c,G⟩_Z and Z_box := box(Z) ⊇ Z, the Hausdorff distance d_H(Z,Z_box) is over-approximated by three bounds: ω_max(Z) := 2‖Σ_p ĝ^(p)‖_2 (with ĝ^(p) zeroed at the (first) index i* attaining ‖g^(p)‖_∞), ω_rad(Z) := Σ_p ‖g^(p)‖_2, and ω_cut(Z) := √2 Σ_p ‖g^(p)‖_2 √(1 - Σ_i (g^(p)_i)^4/‖g^(p)‖_2^4). | ω_max in [`HausdorffDist2IntervalLeMax.lean`](../../src/CORALean/ContSet/Zonotope/Real/Theorems/HausdorffDist2IntervalLeMax.lean), ω_rad in [`HausdorffDist2IntervalLe.lean`](../../src/CORALean/ContSet/Zonotope/Real/Theorems/HausdorffDist2IntervalLe.lean) and ω_cut in [`HausdorffDist2IntervalLeCut.lean`](../../src/CORALean/ContSet/Zonotope/Real/Theorems/HausdorffDist2IntervalLeCut.lean) — each at `hausdorffDist₂`, the Euclidean distance of `Def. 2` (`Vec ℝ n`'s own norm being the supremum one); see the finding below | `correct` |
| `Def. 3` | (Convergence Order of Classical ODE Solvers) The order of a solver for ẋ = f(x,t) is the q∈N_0 with local truncation error ε_{Δt,loc} := \|ξ_ex(Δt;t_0,x_0) - ξ̂(Δt;t_0,x_0)\| ≤ cΔt^{q+1} for all t_0,x_0, with c independent of t_0, x_0 and Δt. | [`ConvergenceOrder.lean`](../../src/CORALean/Global/ConvergenceOrder.lean) — `ξex` and `ξhat` are plain functions of `(Δt,t0,x0)`, not tied to any particular ODE; the binder order puts `c` first, ahead of `Δt`, `t0` and `x0`, which is the definition's whole content | `correct` |
| `Def. 4` | (Errors of Set-based Solvers) For a set-based approximation R = R̂ ⊕ R_abs, the local abstraction error at t_k is ε_{k,loc} := ‖d(box(R_abs(Δt;t_k,R(t_k))))‖_∞, and the global accumulated abstraction error over N steps is ε_N := ‖d(box(R(t_end) ⊖ R̂(t_end)))‖_∞. | [`LocalAbstrErr.lean`](../../src/CORALean/ContDynamics/NonlinearSys/Operations/LocalAbstrErr.lean) and [`GlobalAbstrErr.lean`](../../src/CORALean/ContDynamics/NonlinearSys/Operations/GlobalAbstrErr.lean), both over `CORALean.boxDiameter`, which is `d(box(·))` of a bare set — a Minkowski difference is not a representation and has no `Interval.radius` to double. `‖·‖_∞` is the norm `Vec ℝ n` already carries, so no conversion is needed. (28)'s two forms are shown equal in [`GlobalAbstrErrEqLocalAbstrErr.lean`](../../src/CORALean/ContDynamics/NonlinearSys/Theorems/GlobalAbstrErrEqLocalAbstrErr.lean), under the hypotheses the finding below names | `underspecified` — the two forms in (28) agree only under convexity and cancellation, which `Alg. 1`'s zonotopes meet |
| `Lemma 2` | (Local and Global Abstraction Error) For solvers of the form (10), ε_N ≤ (c/Δt)·max_{1≤ℓ≤N} ε_{ℓ,loc}, with a constant c that may depend on t_end but not on Δt or N. | [`GlobalAbstrErrLeLocalAbstrErrOfSolver.lean`](../../src/CORALean/ContDynamics/NonlinearSys/Theorems/GlobalAbstrErrLeLocalAbstrErrOfSolver.lean) — at one fixed linearization matrix `A ≠ 0`, with every `R̂_k` nonempty and bounded and every `R_abs,k` nonempty, convex and compact, as the zonotopes `Alg. 1` produces are; see the finding below | `underspecified` — proof uses one fixed linearization matrix `A`, which the statement does not say; formalized at fixed `A ≠ 0` |
| `Def. 5` | (Gain Function) The gain over the time span h with relative increment δ∈[0,1] is φ(h;δ) = max_i φ_i(h;δ), where φ_i(h;δ) = d_i(box(R^∞_abs(δh)))/d_i(box(R^∞_abs(h))). | [`Gain.lean`](../../src/CORALean/ContDynamics/NonlinearSys/Operations/Gain.lean) over [`GainDim.lean`](../../src/CORALean/ContDynamics/NonlinearSys/Operations/GainDim.lean), both over [`AbstrSolInf.lean`](../../src/CORALean/ContDynamics/NonlinearSys/Operations/AbstrSolInf.lean), which is (32) itself — an infinite Minkowski sum has no generator matrix, so nothing in `ContSet` names it and it is the `Set` of what the series sums to over independent choices from Ψ(h). `A` and `Ψ` are functions of h, since (6)'s linearization point moves with the step. Where the denominator vanishes Lean's `x / 0 = 0` applies, which is not the paper's reading; the nonvanishing hypothesis belongs to whatever reads φ_i, as it does in (19). `Prop. 1` is what holds `AbstrSolInf` against the paper, and it is proved | `correct` |
| `Prop. 1` | (Diameter of Set of Abstraction Errors) If Ψ(h) is the zonotope ⟨c(h),G(h)⟩_Z, then d_i(box(R^∞_abs(h))) = 2 Σ_{p≥0} h^{p+1}/(p+1)! ·‖A^p(h)G(h)‖_{1,i}, the 1-norm of the i-th row. | [`BoxDiameterAbstrSolInf.lean`](../../src/CORALean/ContDynamics/NonlinearSys/Theorems/BoxDiameterAbstrSolInf.lean) — the exact `=`, with both extremes attained rather than bounded, and `h ≥ 0` its only hypothesis; see the finding below. Generators are a family and not a matrix here, so ‖A^p(h)G(h)‖_{1,i} reads Σ_j \|(A^p(h) g^(j))_i\|, and Ψ(h) is asked to be a zonotope at this h alone, which is all (35) uses | `underspecified` — `h ≥ 0` is left implicit |
| `Lemma 3` | (Expansion of Coefficients) For smooth f, A(h) and G(h) are smooth and every coefficient is either ‖A^p(h)G(h)‖_{1,i} = h^{q^(p)_i}‖a^(p)_i + b^(p)_i(h)‖_1 with q^(p)_i∈N_0, a^(p)_i ≠ 0, b^(p)_i(h)=O(h), or identically 0 (convention: q^(p)_i = ∞, a^(p)_i = 0); and Q^(p)_i(h) = ‖a^(p)_i + b^(p)_i(h)‖_1 is non-negative and piecewise smooth. | [`RowNormExpansionOfAnalytic.lean`](../../src/CORALean/ContDynamics/NonlinearSys/Theorems/RowNormExpansionOfAnalytic.lean) — proved for an *analytic* right-hand side and not for a smooth one: the printed dichotomy is false as stated, and the finding below gives the counterexample. `≡ 0` reads as vanishing on a neighbourhood of 0, which is what analyticity gives and all the limit h→0 uses; a^(p)_i is a vector of m generator coefficients rather than (36)'s scalar, ‖·‖_1 there being the 1-norm of a *row* of A^p(h)G(h); and Q^(p)_i is shown continuous at 0 rather than piecewise smooth, continuity being what `Thm. 2` and `Prop. 2` read off it. Analyticity is asked of the entries of A and G, so no norm has to be put on a matrix; [`RowNormExpansion.lean`](../../src/CORALean/ContDynamics/NonlinearSys/Counterexamples/RowNormExpansion.lean) — `G(h) = exp(-1/h)` (smooth, `0` for `h ≤ 0`) is neither zero near `0` nor `h^q` times a factor tending to a nonzero vector **Counterexample:** `rowNorm_expansion_counterexample` | `fixed` — dichotomy false for merely smooth `f` (`exp(−1/h²)`); formalized for analytic `f` |
| `Thm. 2` | (Limit Gain) For smooth f, lim_{h→0} φ_i(h;δ) = δ^{q_i+1}, where q_i is the index j at which the coefficient sum Σ_{p+q^(p)_i = j} ‖a^(p)_i‖_1 first fails to vanish (Eq. (40); see the finding below). | [`GainDimTendstoPow.lean`](../../src/CORALean/ContDynamics/NonlinearSys/Theorems/GainDimTendstoPow.lean) — the limit itself, as h→0 from the right and for every δ ≥ 0. Its hypothesis is the expansion in factored form, d_i(box(R^∞_abs(t))) = t^{q_i+1}·g(t) with g continuous at 0 and g(0) ≠ 0: that is `Lemma 3` grouped by j = p + q^(p)_i, read at the *lowest* such j per the (40) finding, and g(0) ≠ 0 is also the nonvanishing denominator (19) asks for and `Def. 5` defers to its readers. What the hypothesis stands in for is the one step of the paper's proof that is not justified there — passing to the limit inside the series termwise, with no uniform control over p; see the finding below. δ ≤ 1 is not needed for the limit to exist, only for it to be a contraction | `proof-gap` — limit taken termwise in the series without uniform control in `p`; that step is a hypothesis here |
| `Def. 6` | (Gain Order of Set-based Solvers) q := min_i q_i is the gain order of the method and q_i that of the i-th dimension; the method has zero abstraction error iff q = ∞. | [`GainOrder.lean`](../../src/CORALean/ContDynamics/NonlinearSys/Operations/GainOrder.lean) over [`GainOrderDim.lean`](../../src/CORALean/ContDynamics/NonlinearSys/Operations/GainOrderDim.lean), at `ℕ∞`, where `∞` is a value of the definition rather than a failure case and `sInf ∅ = ⊤` is the convention (40) needs. Stated as the *minimum* of (40), per the finding below. The closing sentence is [`GainOrderEqTopIff.lean`](../../src/CORALean/ContDynamics/NonlinearSys/Theorems/GainOrderEqTopIff.lean), which carries `Lemma 3`'s convention as a hypothesis, and with (40) as printed, a maximum, that sentence is false, one dimension with every coefficient non-zero giving `q = ∞` ([`GainOrderMax.lean`](../../src/CORALean/ContDynamics/NonlinearSys/Counterexamples/GainOrderMax.lean)) **Counterexample:** `gainOrder_max_eq_top_iff_counterexample` | `fixed` — eq. (40) prints a maximum where a minimum is meant (the maximum is `∞` for infinite series), so the printed definition gives the wrong gain order on ordinary inputs |
| `Prop. 2 (gain bound)` | (Derivative of Gain, second half) For fixed h, if every Q^(p)_i is constant on [0,h], then φ_i(t;δ) ≤ δ^{q_i+1} for all t∈[0,h] (42), and so (43). | [`GainDimLePow.lean`](../../src/CORALean/ContDynamics/NonlinearSys/Theorems/GainDimLePow.lean) — (42), and with it (43). With every Q^(p)_i constant on [0,h], shrinking the span to δt multiplies the p-th term of (35) by δ^{p+q^(p)_i+1}, and p + q^(p)_i ≥ q_i for every term that survives — (40) as a minimum, which is how `GainOrderDim` has it — so δ ≤ 1 pulls δ^{q_i+1} out of the whole series at once. That is shorter than the paper's route through (41), needs no continuity, no monotonicity and no proof by contradiction, and holds on all of [0,h] | `correct` |
| `Prop. 2 (derivative)` | (Derivative of Gain, first half) If all Q^(p)_i are differentiable at 0, then lim_{h→0} dφ_i(h;δ)/dh ≤ 0 for δ∈[0,1] (41). | [`GainDimDerivTendsto.lean`](../../src/CORALean/ContDynamics/NonlinearSys/Theorems/GainDimDerivTendsto.lean) — the limit itself, `δ^{q_i+1}(δ − 1) g'(0)/g(0)`, for the width in the factored form `t^{q_i+1}g(t)` of `Thm. 2` with `g` differentiable near 0 and `g'` continuous at 0 (the hypothesis that stands in for differentiating the series termwise), [`GainDimDerivLimitNonpos.lean`](../../src/CORALean/ContDynamics/NonlinearSys/Theorems/GainDimDerivLimitNonpos.lean) — (41) with the condition `0 ≤ g'(0)/g(0)` it needs, [`GainDeriv.lean`](../../src/CORALean/ContDynamics/NonlinearSys/Counterexamples/GainDeriv.lean) — `n = 1`, `A = 0`, `Ψ(h) = ⟨0, 1 − h⟩`: smooth, every Q^(p)_i differentiable at 0 with Q^(0)_i(0) ≠ 0, and `dφ/dh → 1/4` at `δ = 1/2`. **Counterexample:** `gainDim_deriv_counterexample` | `fixed` — the limit exists but is not always ≤ 0: the Q̇^(p)_i(0) terms of the numerator, which the proof's (B.5) drops, can make it positive; true when `g'(0)/g(0) ≥ 0`, in particular when the Q^(p)_i are constant; see Findings |
| `Alg. 1` | "Reachability analysis of continuous-time nonlinear systems using abstractions in the state space": the on-the-fly abstraction loop (linearization point, Taylor expansion, `linReach`, abstraction-error fixed point, addition, order reduction), stated for nonlinear differential-algebraic systems and specializing to the other system classes. | [`AbstrReach.lean`](../../src/CORALean/ContDynamics/NonlinearSys/Operations/AbstrReach.lean) — one `let` per printed line, for the ordinary differential equations the paper obtains "by omitting each occurrence of the algebraic equation", the differential-algebraic generality being what the finding below leaves open. Line 3 is [`LinPoint.lean`](../../src/CORALean/ContDynamics/NonlinearSys/Operations/LinPoint.lean), lines 8-11 are [`AbstrErrLoop.lean`](../../src/CORALean/ContDynamics/NonlinearSys/Operations/AbstrErrLoop.lean), and line 12's `abstrSol` is `LinearSys.inputSolution` at Ψ, (8) being that operation's formula exactly. Lines 4-5 are the caller's, nothing here differentiating `f`. What the loop guarantees is [`AbstrErrLoopFixed.lean`](../../src/CORALean/ContDynamics/NonlinearSys/Theorems/AbstrErrLoopFixed.lean) and what line 18 collects is [`SubsetAbstrReach.lean`](../../src/CORALean/ContDynamics/NonlinearSys/Theorems/SubsetAbstrReach.lean). In floats this step is `RelinStepFloat.lean`, which checks a region where the paper's lines 8-11 enlarge an error | `correct` |
| `Alg. 2` | "Adaptively-tuned reachable set computation for one step k>1": updates the finite horizon h_k from the previous gain, runs the step twice — once to compute R_abs(h) and the optimal Δt*, once to compute the reachable set with it — and returns the next abstraction order κ_{k+1}, horizon h_k and gain φ^(1)_k. | [`AdaptStep.lean`](../../src/CORALean/ContDynamics/NonlinearSys/Operations/AdaptStep.lean) — lines 1-18, with lines 3-6 the half both passes share; the second pass runs the error loop at both orders `κ` unconditionally, where the paper computes the other order's `R_abs` only when (46) fires — same value, different cost and failure mode. Its three tuning subroutines compute rather than choose classically: [`OptDeltat.lean`](../../src/CORALean/ContDynamics/NonlinearSys/Operations/OptDeltat.lean) is (57) and the descent (58) is evaluated by, [`EstimateGain.lean`](../../src/CORALean/ContDynamics/NonlinearSys/Operations/EstimateGain.lean) solves (56) by bisection, and [`TuneAbstrOrder.lean`](../../src/CORALean/ContDynamics/NonlinearSys/Operations/TuneAbstrOrder.lean) is (46)–(47). The first two are held to [`OptDeltatDescent.lean`](../../src/CORALean/ContDynamics/NonlinearSys/Theorems/OptDeltatDescent.lean) and [`EstimateGainBracket.lean`](../../src/CORALean/ContDynamics/NonlinearSys/Theorems/EstimateGainBracket.lean), and the step itself to [`AdaptStepInvariant.lean`](../../src/CORALean/ContDynamics/NonlinearSys/Theorems/AdaptStepInvariant.lean). §5.1's η and §5.3's reduction order are parameters here, not tuned; see the finding below. In floats the step is [`AdaptStepFloat.lean`](../../src/CORALean/ContDynamics/NonlinearSys/Operations/AdaptStepFloat.lean) and the loop `AdaptRunFloat.lean`: the abstraction-error loop of lines 7-11 becomes the checked region of [`OrderStepFloat.lean`](../../src/CORALean/ContDynamics/NonlinearSys/Operations/OrderStepFloat.lean), `κ = 1` the slope remainder and `κ = 2` the Hessian one, `R_abs` enters the tuning only as a difference of box radii and diameters against `AdaptLinPassFloat.lean`, and the tuning subroutines are restated over the scalar as the `…Float` files beside their real ones | `underspecified` — line 10 reads a gain that line 16 has not computed yet; the previous step's gain is meant |

## Findings

**`Thm. 1` — the norm the three bounds are proved at is not the one `Vec ℝ n` carries.**
`Vec ℝ n` is `Fin n → ℝ`, and Mathlib's `Pi` instance gives it the *supremum* norm, so
`Metric.hausdorffDist` there is the sup-norm distance and not `Def. 2`. Rather than move the
type, `hausdorffDist₂` takes Mathlib's distance through `toEuclidean : Vec ℝ n ≃L[ℝ]
EuclideanSpace ℝ (Fin n)`, which is `Def. 2` verbatim and costs two translation lemmas; all three
bounds are proved at it. The sup-norm analogue of ω_rad stands separately as
`Zonotope.hausdorffDist_interval_le` — `∑ₚ ‖g⁽ᵖ⁾‖_∞` is not `∑ₚ ‖g⁽ᵖ⁾‖₂` and neither implies the
other, so both are kept. ω_cut is proved without the Bauer maximum principle the paper's appendix
uses to restrict the coefficients to the vertices of `[-1,1]^n`: the quantity it bounds is half a
double sum of squared coefficient differences, whose diagonal vanishes, and `(νᵢ-νⱼ)² ≤ 4` off the
diagonal then gives the same estimate over the whole box.
[`HausdorffDist2IntervalLe.lean`](../../src/CORALean/ContSet/Zonotope/Real/Theorems/HausdorffDist2IntervalLe.lean),
[`HausdorffDist2IntervalLeMax.lean`](../../src/CORALean/ContSet/Zonotope/Real/Theorems/HausdorffDist2IntervalLeMax.lean),
[`HausdorffDist2IntervalLeCut.lean`](../../src/CORALean/ContSet/Zonotope/Real/Theorems/HausdorffDist2IntervalLeCut.lean)

**Eq. (40), in `Thm. 2`.** The gain order is defined as q_i = max{ j∈N_0 \| Σ_{p+q^(p)_i = j}
‖a^(p)_i‖_1 ≠ 0 }, but the maximum is a minimum. The limit h→0 is decided by the
*lowest*-order term of d_i(box(R^∞_abs(h))) = 2 Σ_j h^{j+1} Σ_{p+q^(p)_i=j} ‖a^(p)_i +
b^(p)_i(h)‖_1/(p+1)!, and for a system with infinitely many non-vanishing coefficients the
printed maximum is ∞ — which by `Def. 6` would say the method has zero abstraction error.
The note printed directly under (40) describes when the sum *vanishes* ("either there does
not exist a tuple (p,q^(p)_i) such that p + q^(p)_i = j, or ... a^(p)_i = 0"), i.e. the
negation of the condition as printed, and the proof uses only that the coefficient at q_i
is non-zero. Reading (40) as a minimum makes the theorem, its proof, and `Def. 6`'s
"q = ∞ iff zero abstraction error" agree.

**`Lemma 2` — both halves now proved, at one fixed `A`; a re-linearizing run stays
out of scope, stated rather than silently inherited.**
Appendix B's proof has two parts: first, (10)'s recursion — sharing `P(τ_k)`
between `R` and `R̂` — is expanded, via the triangle inequality and a Taylor
bound on `e^{AΔt}`, into `ε_{k+1} ≤ (1+LΔt)ε_k + ε_{k,loc}` for an `L`
Lipschitz in `Δt` over `[0,t_end]`; second, that recursion is unrolled by the
discrete Grönwall argument the paper cites from Süli & Mayers to reach (30).
The second part is `aux_gronwall` in
[`GlobalAbstrErrLeLocalAbstrErr.lean`](../../src/CORALean/ContDynamics/NonlinearSys/Theorems/GlobalAbstrErrLeLocalAbstrErr.lean),
landed earlier and unchanged. The first part — `hstep` — was there taken as a
hypothesis; it is now derived, in
[`GlobalAbstrErrStepOfSolver.lean`](../../src/CORALean/ContDynamics/NonlinearSys/Theorems/GlobalAbstrErrStepOfSolver.lean),
from a formal reading of (B.1)–(B.2) themselves: rather than cancel the shared
`P(τ_k)` through `⊖` — the erosion `minkowskiDiff` on a bare set is not a group
subtraction, so `(X+P)⊖(Y+P) = X⊖Y` fails as soon as the
minuend is non-convex: `X={0,2}`, `Y={0}`, `P=[0,2]` gives `X⊖Y = {0,2}` against
`[0,4]⊖[0,2] = [0,2]`. No interval triple witnesses it — for convex compact
operands Rådström cancellation makes the two sides equal, which is why
`Global/Radstrom.lean` had to be proved for `Def. 4`'s own step — the recursion is tracked
forward as an explicit, honestly-composed error set `E(k+1) := e^{AΔt}E(k) ⊞
Rabs(k)`, `E(0) = {0}`, giving `R(k) = R̂(k) + E(k)` by pure reassociation; `Def.
4`'s two forms of the local error, already proved equal, then read `hstep` off
two `boxDiameter` facts — subadditivity under `⊕`, and a bound under a linear
image by its operator norm — with `L := ‖A‖e^{t_end‖A‖}` from an unconditional
Taylor bound `‖e^{tA}-1‖ ≤ t‖A‖e^{t‖A‖}` (valid for every `t ≥ 0`, not only
small `t`, unlike the tree's existing geometric-series remainder bound).
`A ≠ 0` is the one restriction beyond the paper's own: `aux_gronwall` divides
by `L`, needing `‖A‖ > 0`.
The restriction the paper's own proof carries but its statement does not is
kept explicit rather than inherited silently: (B.1)–(B.2) use one fixed matrix
`A`, dropping its `Δt`-dependency "for ease of notation", but say nothing
about it varying with the step index `k` — which a re-linearizing run (`Alg.
1`, applied `N` times) does.
[`GlobalAbstrErrLeLocalAbstrErrOfSolver.lean`](../../src/CORALean/ContDynamics/NonlinearSys/Theorems/GlobalAbstrErrLeLocalAbstrErrOfSolver.lean)
composes both halves into `[1, Lemma 2]` outright, for that fixed-`A` reading;
a re-linearizing run — the honest general statement, with a uniform Lipschitz
bound over every step's own `A_k` — is not attempted here.

**`Def. 4` — (28)'s two forms of the local error are equal only under cancellation.**
(28) writes ε_{k,loc} both as `d(box(R ⊖ R̂))_∞` and as `d(box(R_abs))_∞`, on the strength of
`R = R̂ ⊕ R_abs`. Only one direction of that is free: `R_abs ⊆ (R̂ ⊕ R_abs) ⊖ R̂` always, while
the reverse is Rådström cancellation and needs `R_abs` convex and closed and `R̂` nonempty and
bounded. Every step of `Alg. 1` meets those — both sets are zonotopes — so the row flips and the
hypotheses sit on the theorem rather than on either definition, which are about any solver at all.
[`GlobalAbstrErrEqLocalAbstrErr.lean`](../../src/CORALean/ContDynamics/NonlinearSys/Theorems/GlobalAbstrErrEqLocalAbstrErr.lean)

**`Prop. 1` — (35) holds for h ≥ 0, and asks nothing else.** The proposition is stated over a
time span and reads h^{p+1} at face value, so h ≥ 0 is left implicit; at h < 0 the odd-index
coefficients change sign and the identity would carry |h|^{p+1} instead. That is the one
hypothesis the formalization adds. No convergence condition joins it: the term
h^{p+1}/(p+1)!·‖A^p(h)G(h)‖_{1,i} is under h·R·(h‖A(h)‖)^p/p! with R the zonotope's reach, and
the exponential series dominates that for every A(h) and every Ψ(h) — which is also what makes
R^∞_abs(h) nonempty and its box finite, neither of which (32) says. The maxima the Appendix-B
proof takes through Bauer's maximum principle are support values of a zonotope in the directions
±e_i, attained at a sign pattern of the generators and independent across the summands, so the
row flips on an `=` and not on a `⊆`.
[`BoxDiameterAbstrSolInf.lean`](../../src/CORALean/ContDynamics/NonlinearSys/Theorems/BoxDiameterAbstrSolInf.lean)

**`Lemma 3` — the dichotomy is false for a merely smooth f.** (36) and (37) say that every
coefficient ‖A^p(h)G(h)‖_{1,i} is either h^{q^(p)_i}‖a^(p)_i + b^(p)_i(h)‖_1 with a^(p)_i ≠ 0 and
b^(p)_i(h) = O(h), or identically 0. A smooth function can be neither: h ↦ exp(-1/h²), extended by
0 at the origin, is C^∞, vanishes only at 0, and is o(h^q) for every q, so it has no leading term
and is not identically zero. Appendix B is where the gap shows — "if for all N ∈ N_0 such an index
does not exist, it trivially follows that [A^p(h)G(h)]_i ≡ 0" reads a vanishing Taylor series as a
vanishing function, which is what *analytic* means rather than something *smooth* implies. The
hypothesis that makes the lemma true is that f, and hence A and G, are real-analytic; that is what
the formalization asks, entrywise, so that nothing has to put a norm on a matrix. Everything
downstream uses the lemma's conclusion and not its hypothesis, so `Thm. 2`, `Def. 6` and `Prop. 2`
are unaffected beyond inheriting it.
[`RowNormExpansionOfAnalytic.lean`](../../src/CORALean/ContDynamics/NonlinearSys/Theorems/RowNormExpansionOfAnalytic.lean)

**`Thm. 2` — the limit is taken inside the series without uniform control.** The proof rewrites
d_i(box(R^∞_abs(h))) as 2 Σ_j h^{j+1} Σ_{p+q^(p)_i=j} ‖a^(p)_i + b^(p)_i(h)‖_1/(p+1)! and lets
h→0 term by term, "using the fact that b^(p)_i = O(h)". Each b^(p)_i is O(h) for its own p; making
the tail of the j-sum vanish needs an estimate uniform in p, which `Lemma 3` does not supply and
which does not follow from `Prop. 1`'s majorant either — that one bounds ‖A^p(h)G(h)‖_{1,i}, while
the tail is in Q^(p)_i(h) = h^{-q^(p)_i}‖A^p(h)G(h)‖_{1,i}, which it says nothing about. So the
formalization takes the conclusion of that step as its hypothesis — d_i(box(R^∞_abs(t))) =
t^{q_i+1}·g(t) with g continuous at 0 and g(0) ≠ 0 — and proves the limit from it. `Prop. 2`'s
constant-Q^(p)_i case is where the step is elementary, and that case is proved outright, straight
from (35) and with no limit taken at all.
[`GainDimTendstoPow.lean`](../../src/CORALean/ContDynamics/NonlinearSys/Theorems/GainDimTendstoPow.lean),
[`GainDimLePow.lean`](../../src/CORALean/ContDynamics/NonlinearSys/Theorems/GainDimLePow.lean)

**`Prop. 2 (derivative)` — (41) drops the derivatives of the Q^(p)_i.** The proof differentiates
φ_i = d_i(box(R^∞_abs(δh)))/d_i(box(R^∞_abs(h))) and arrives at (B.5), whose numerator carries
`[δ^{j+1} − φ_i][(j+1)Q^(p)_i(δh) + h Q̇^(p)_i(δh)]`. Differentiating the two widths gives
`(j+1)δ^{j+1}h^j Q(δh) + …` for the numerator width and `φ_i (j+1)h^j Q(h) + …` for the
denominator one, so `Q` is evaluated at `δh` in the term multiplied by `φ_i` where it should be
at `h`; the difference `Q(δh) − Q(h) = (δ − 1)h Q̇(0) + o(h)` is of exactly the order of the terms
the proof keeps, and the `Q̇` terms of the numerator are likewise at `δh` throughout.
With the width written `t^{q+1}g(t)` near 0
(`Thm. 2`'s factored form), `φ_i = δ^{q+1}g(δh)/g(h)` and, for `g` continuously differentiable,
`dφ_i/dh → δ^{q+1}(δ − 1) g'(0)/g(0)`. Here `g'(0)` is the coefficient of `t^{q+2}` *plus* the
`Q̇^(p)_i(0)` of the lowest-order coefficient; the paper's closing formula keeps only the first,
which is non-negative, hence the sign. The second can be negative: `A ≡ 0`, `n = 1`,
`Ψ(h) = ⟨0, 1 − h⟩` gives `Q^(0)_i(h) = |1 − h|` (smooth, `Q^(0)_i(0) = 1`, every other
`Q^(p)_i` zero), width `2h(1 − h)`, `φ_i(h;δ) = δ(1 − δh)/(1 − h)` and
`dφ_i/dh = δ(1 − δ)/(1 − h)² → δ(1 − δ) = 1/4` at `δ = 1/2`, increasing, not decreasing. (As with
`Lemma 3`, the example is a pair of smooth functions `A(h)`, `G(h)`; the paper's own `A(h)` and
`G(h)` come from `f` and are not shown to realise it.) The repair is the sign condition
`g'(0)/g(0) ≥ 0`, under which (41) holds, and which the constant-Q^(p)_i case (42) satisfies since
`g'(0)` is then the non-negative coefficient of `t^{q+2}`. The consequence the paper draws in
Sec. 4.3, that φ is decreasing on a small interval and so (43), is `Prop. 2 (gain bound)`'s
(42) and is proved without it.
[`GainDimDerivTendsto.lean`](../../src/CORALean/ContDynamics/NonlinearSys/Theorems/GainDimDerivTendsto.lean),
[`GainDimDerivLimitNonpos.lean`](../../src/CORALean/ContDynamics/NonlinearSys/Theorems/GainDimDerivLimitNonpos.lean),
[`GainDeriv.lean`](../../src/CORALean/ContDynamics/NonlinearSys/Counterexamples/GainDeriv.lean)

**`Alg. 1` — lines 4-5 are supplied, and the differential-algebraic half is not taken on.**
`taylor` and `linSys` read derivatives of `f` off the linearization point, and nothing in this
tree differentiates `f`: `AbstractionError` is a certificate and `Linearize` takes `A` as given,
so `abstrStep` asks the caller for the `A` and `B` a linearization at line 3's point would yield,
exactly as `LinStep` carries them. The certificate consequently sits on the theorems rather than
in the definition. The algebraic equation is omitted throughout — `linPoint` has no `y✱`, `linSys`
no `Ỹ Z̃⁻¹` elimination and the loop no `R_y(t_{k+1})` — which is the specialization the paper
states directly under its `Alg. 1`; the full differential-algebraic form would need a system type,
that elimination and the Newton–Raphson solve of (6), none of which the tree has. One further
departure: (12) puts the particular solution inside the convex hull, while
`LinearSys.timeIntervalStep` computes `conv(R, e^{AΔt}R) ⊕ F R` and the particular solution is
added outside it, as CORA does. That encloses (12) whenever `P(τ_k)` is convex and holds the
origin — which is what (12)'s own `0 ∈ U` gives — but nothing here proves it; it is recorded, not
discharged.
[`AbstrReach.lean`](../../src/CORALean/ContDynamics/NonlinearSys/Operations/AbstrReach.lean)

**`Alg. 2` — line 10 is passed a gain that line 16 has not computed yet.**
Line 10 reads `∆t* ← optDeltat(h_k, φ^(1)_k, r^(1)_abs,k)`, but `φ^(1)_k` is the output of line 16,
three lines below and outside the `for` loop; the algorithm's own input list supplies
`φ^(1)_{k-1}`, the gain of the last step, and line 1 uses exactly that. So line 10's subscript is
one too high and the value available there is the previous step's gain, which is what the
formalization passes. Two things the row does not cover: §5.1's propagation orders `η_lin` and
`η_abs`, criteria (44) and (45), and §5.3's reduction order, criterion (48), are parameters of
`adaptStep` rather than tuned in it — `linReachAdaptive`, `abstrSolAdaptive` and `redAdaptive` are
`linReach`, `abstrSol` and `red` at orders the caller fixes. The CDC paper's `Alg. 3`,
[`AdaptSetOrder.lean`](../../src/CORALean/ContSet/Zonotope/Real/Operations/AdaptSetOrder.lean), is the same
idea as (48) at a different bound.
[`AdaptStep.lean`](../../src/CORALean/ContDynamics/NonlinearSys/Operations/AdaptStep.lean)

## Cited without a result

These name the paper as a whole. A locator would put each in a row above.

* [`AdaptLinPassFloat.lean`](../../src/CORALean/ContDynamics/NonlinearSys/Operations/AdaptLinPassFloat.lean)
* [`AdaptRunFloatOuter.lean`](../../src/CORALean/ContDynamics/NonlinearSys/Theorems/AdaptRunFloatOuter.lean)
* [`AdaptStepFloatOuter.lean`](../../src/CORALean/ContDynamics/NonlinearSys/Theorems/AdaptStepFloatOuter.lean)
* [`CenterAbstrStepFloat.lean`](../../src/CORALean/ContDynamics/NonlinearSys/Operations/CenterAbstrStepFloat.lean)
* [`EstimateGainSearch.lean`](../../src/CORALean/ContDynamics/NonlinearSys/Operations/EstimateGainSearch.lean)
* [`EstimateGainSearchFloat.lean`](../../src/CORALean/ContDynamics/NonlinearSys/Operations/EstimateGainSearchFloat.lean)
* [`GainMaxFloat.lean`](../../src/CORALean/ContDynamics/NonlinearSys/Operations/GainMaxFloat.lean)
* [`InterpGain.lean`](../../src/CORALean/ContDynamics/NonlinearSys/Operations/InterpGain.lean)
* [`InterpGainFloat.lean`](../../src/CORALean/ContDynamics/NonlinearSys/Operations/InterpGainFloat.lean)
* [`LinReachAdaptiveCora1D.lean`](../../src/CORALean/ContDynamics/NonlinearSys/Counterexamples/LinReachAdaptiveCora1D.lean)
* [`OptDeltatSearch.lean`](../../src/CORALean/ContDynamics/NonlinearSys/Operations/OptDeltatSearch.lean)
* [`OptDeltatSearchFloat.lean`](../../src/CORALean/ContDynamics/NonlinearSys/Operations/OptDeltatSearchFloat.lean)
* [`LinReachAdaptiveCora1D.lean`](../../src/CORALean/ContDynamics/NonlinearSys/Counterexamples/LinReachAdaptiveCora1D.lean)
* [`OrderStepFloatOuter.lean`](../../src/CORALean/ContDynamics/NonlinearSys/Theorems/OrderStepFloatOuter.lean)
* [`ReachSizeEstimate.lean`](../../src/CORALean/ContDynamics/NonlinearSys/Operations/ReachSizeEstimate.lean)
* [`ReachSizeEstimateFloat.lean`](../../src/CORALean/ContDynamics/NonlinearSys/Operations/ReachSizeEstimateFloat.lean)
* [`TuneDeltatInitFloat.lean`](../../src/CORALean/ContDynamics/NonlinearSys/Operations/TuneDeltatInitFloat.lean)
