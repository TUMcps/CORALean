# Inner Approximations of Reachable Sets for Nonlinear Systems using the Minkowski Difference

M. Wetzlinger, A. Kulmburg and M. Althoff. "Inner Approximations of Reachable Sets for Nonlinear Systems using the Minkowski Difference". IEEE Control Systems Letters, 8:2033-2038, 2024.

**Source:** https://mediatum.ub.tum.de/doc/1749456/1749456.pdf (the accepted author's version on TUM's repository, "accepted for publication in IEEE Control Systems Letters", doi:10.1109/LCSYS.2024.3421194, 6 pages, read in full; text extracted with `pypdf`). Volume and pages from the published record; the typeset article was not reachable. CORA cites the paper in `nonlinearSys/private/priv_reachInnerMinkdiff.m` and `contDynamics/linReachInner.m` without result numbers.  
**Inventory:** confirmed (Definitions 1-4, Lemma 1, Remark 1, Propositions 1-2 and Algorithm 1, each with its own counter; equations (1)-(26), of which the rows below are the displays that make a claim; Table I)

An inner approximation of the reachable set of a nonlinear system computed directly, without
an outer approximation first: the affine part's reachable set minus — Minkowski difference —
the abstraction error's. The time-point step (`Prop. 1`) rests on `Lemma 1`, a fixed-point
argument (Brouwer), and the time-interval step (`Prop. 2`) on `Lemma 1` again; `Alg. 1` runs
both with polytopes and constrained zonotopes. Formalized, on CORALean's own proof of
Brouwer's theorem (`exists_fixedPoint_of_isCompact_convex`): `Lemma 1` as printed, `Prop. 1`
from the representation (21), whose printed proof needs the error set's convexity rather than
`R_aff`'s, (21) itself from a linearization's abstraction-error certificate, so that `Prop. 1`
holds for a linearized step, and `Remark 1`'s counterexample, as is the closed form of the
constant-input solution (12). `Prop. 2` is false, for a nonconvex initial set, which it admits,
and for a convex one (a box, under a linear shear) alike. `Alg. 1` is written line by line
over exact sets; its time-point sets are inner approximations, step by step, and its output, the
union of the time-interval sets, is not, by `Prop. 2`'s convex counterexample run through the
algorithm. The rest is restated from the conservative-linearization papers
the method is built on.

## Results

| Result | What it says | In CORALean | Class |
|---|---|---|---|
| `Eq. 1` | (Minkowski difference) S₁ ⊖ S₂ := {s \| s ⊕ S₂ ⊆ S₁} = {s \| ∀ s₂ ∈ S₂: s + s₂ ∈ S₁}. | n/a — the standard definition, restated; it is `minkowskiDiff` | `restated` |
| `Eq. 2` | For compact, convex, nonempty S₁, S₂, S₃: S₁ ⊖ (S₂ ⊕ S₃) = (S₁ ⊖ S₂) ⊖ S₃ = (S₁ ⊖ S₃) ⊖ S₂. | n/a — restated from Danilov and Koshevoy 2000 [15, Eq. (2)]; `minkowskiDiff_add_assoc` has it for all sets | `restated` |
| `Eq. 3` | conv(S₁ ⊖ S₃, S₂ ⊖ S₃) ⊆ conv(S₁, S₂) ⊖ S₃. | n/a — restated from [16, Lemma 1]; tracked as `Lemma 1` on [Wetzlinger and Althoff 2026](../2026/wetzlinger-tac-backward-reachability.md) | `restated` |
| `Def. 1` | (Exact reachable set) R(t) := {ξ(t; x(0)) \| x(0) ∈ X₀} for ẋ = f(x), and R(τ) = ⋃_{t∈τ} R(t). | [`ReachSet.lean`](../../src/CORALean/ContDynamics/NonlinearSys/Definitions/ReachSet.lean) — `NonlinearSys.reachSet`, over every solution (the one ξ when f is Lipschitz), with inputs that the autonomous case leaves out | `correct` |
| `Eq. 8` | (6)-(7): f(x) = f(x*) + Df(x*)(x - x*) + l(x), l(x) in the Lagrange remainder L(X), so f(x) ∈ w + A(x - x*) ⊕ L(X). | n/a — restated from [18, Eq. (2)]; tracked as `Eq. 2` on [Althoff et al. 2008](../2008/althoff-cdc-conservative-linearization.md) | `restated` |
| `Eq. 9` | L⁽ⁱ⁾(X) is enclosed by [-l̂⁽ⁱ⁾, l̂⁽ⁱ⁾], l̂⁽ⁱ⁾ = ½ max\|x - x*\|ᵀ max D²f⁽ⁱ⁾ max\|x - x*\|. | n/a — restated from [18, Prop. 1]; tracked as `Prop. 1` on [Althoff et al. 2008](../2008/althoff-cdc-conservative-linearization.md) | `restated` |
| `Eq. 10` | R_aff(Δt) = R_hom(Δt) ⊕ R_con(Δt), R_hom(Δt) = e^{AΔt}X₀ (11), the affine dynamics' solution. | n/a — the variation-of-constants solution, restated; tracked as `Eq. 5` on [Althoff and Krogh 2012](../2012/althoff-hscc-avoiding-intersection.md) | `restated` |
| `Eq. 12` | R_con(Δt) = ∫₀^Δt e^{A(Δt-θ)}dθ w = A⁻¹(e^{AΔt} - I)w; for singular A, A⁻¹ is factored into the series of e^{AΔt}. | [`MulExpIntegral.lean`](../../src/CORALean/ContDynamics/LinearSys/MatExp/Theorems/MulExpIntegral.lean), [`ExpIntegralConstInput.lean`](../../src/CORALean/ContDynamics/LinearSys/Theorems/ExpIntegralConstInput.lean) — the integral is `expIntegral A Δt *ᵥ w` (the series, any A), which is A⁻¹(e^{AΔt} - I) for invertible A | `correct` |
| `Eq. 13` | The abstraction error's reachable set is enclosed by ⊕_{j=0}^η A^jΔt^{j+1}/(j+1)! L ⊕ E(Δt)ΔtL. | n/a — restated from [19, Prop. 3.7]; tracked as `Prop. 3.7` on [Althoff's thesis](../2010/althoff-thesis.md) | `restated` |
| `Eq. 14` | R(Δt) ⊆ R_aff(Δt) ⊕ R̂_err, and (15) R(τ₀) ⊆ R̂_aff(τ₀) ⊕ R̂_err. | n/a — restated from [18, Sec. III] | `restated` |
| `Eq. 16` | R̂_aff(τ₀) = conv(X₀, R_aff(Δt)) ⊕ C encloses the affine time-interval solution, C = F(Δt)X₀ ⊕ G(Δt)w (17). | n/a — restated from [19, Sec. 3.2.2] and [16, Eq. (18), (26)] | `restated` |
| `Lemma 1` | For A ⊂ ℝⁿ nonempty, convex, compact, B centrally symmetric around c, φ: A → B continuous and S = {a + φ(a) \| a ∈ A}: A ⊖ B ⊆ S - 2c (19). | [`MinkowskiDiffSubsetOfContinuous.lean`](../../src/CORALean/ContSet/ContSet/Theorems/MinkowskiDiffSubsetOfContinuous.lean) — `minkowskiDiff_subset_of_continuous`, in any finite-dimensional real normed space, the symmetry as `b ∈ B → 2c - b ∈ B`, by Brouwer's theorem as the paper argues | `correct` |
| `Remark 1` | Continuity of φ cannot be dropped: A = B = [-1, 1] gives A ⊖ B = {0}, and φ = sign (sign 0 = 1) gives S = [-2, -1) ∪ [1, 2]. | [`MinkowskiDiffNotSubsetOfDiscontinuous.lean`](../../src/CORALean/ContSet/ContSet/Theorems/MinkowskiDiffNotSubsetOfDiscontinuous.lean) — all three sets as stated, and 0 ∉ S | `correct` |
| `Prop. 1` | (Time-point reachable set) For X₀ compact, nonempty and R̂_err centrally symmetric, R̂(Δt) = R_aff(Δt) ⊖ R̂_err + 2c ⊆ R(Δt), c = cen(R̂_err) (20). | [`MinkowskiDiffAddSubsetReachSet.lean`](../../src/CORALean/ContDynamics/NonlinearSys/Theorems/MinkowskiDiffAddSubsetReachSet.lean), [`MinkowskiDiffSubsetOfContinuousOfConvex.lean`](../../src/CORALean/ContSet/ContSet/Theorems/MinkowskiDiffSubsetOfContinuousOfConvex.lean) — `NonlinearSys.minkowskiDiff_add_subset_reachSet`: e^{AΔt} = `M` invertible, R_con = `v`, R̂_err a convex compact set as (13) makes it; the proof's representation (21) is the hypothesis `herr` (restated from [18], like (14)), the solutions and the field's Lipschitz constant along them (the paper's standing assumption) are hypotheses, and Grönwall gives the continuity of `z` the proof invokes; `minkowskiDiff_subset_of_continuous_of_convex` is `Lemma 1` with `B`, not `A`, convex. [`SubMemInputSolution.lean`](../../src/CORALean/ContDynamics/NonlinearSys/Theorems/SubMemInputSolution.lean), [`MinkowskiDiffInputSolutionSubsetReachSet.lean`](../../src/CORALean/ContDynamics/NonlinearSys/Theorems/MinkowskiDiffInputSolutionSubsetReachSet.lean) — (21) derived from a linearization: `NonlinearSys.IsTrajectory.sub_mem_inputSolution` for a run that stays in the region of an `AbstractionError` certificate `L`, with R̂_err = `inputSolution Δt η L` (13), and with it `NonlinearSys.minkowskiDiff_inputSolution_subset_reachSet`, the proposition for a linearized step, the confinement still a hypothesis | `proof-gap` — the proof applies `Lemma 1` with A = R_aff(Δt) = e^{AΔt}X₀ + R_con, which is not convex for the merely compact X₀ the proposition allows; the statement holds because R̂_err is (Findings) |
| `Prop. 2` | (Time-interval reachable set) For a compact, non-empty X₀ and E = C ⊕ R̂_err (22) centrally symmetric around c, R̂(τ₀) = conv((X₀ ⊖ C) ⊖ R̂_err, R̂(Δt) ⊖ C) + 2c ⊆ R(τ₀) (23). | [`ConvexHullTimeInterval.lean`](../../src/CORALean/ContDynamics/NonlinearSys/Counterexamples/ConvexHullTimeInterval.lean), [`ConvexHullTimeIntervalConvex.lean`](../../src/CORALean/ContDynamics/NonlinearSys/Counterexamples/ConvexHullTimeIntervalConvex.lean) — **Counterexample:** `convexHull_timeInterval_counterexample`: for `ẋ = (0, 1)`, where R̂_err and C vanish, and two squares as X₀, (23) holds a point no run reaches; `convexHull_timeInterval_convex_counterexample`: the same for the shear `ẋ = (x₂, 0)`, where R̂_err and C vanish as well (`A² = 0`), from the box X₀ = [-1/10, 1/10] × [-1, 1] | `false` — false for a nonconvex X₀, which the proposition admits, and for a convex one, all that `Alg. 1` passes, so convexity does not repair it; see Findings |
| `Def. 2` | (Support function) ρ(S, ℓ) := max_{s∈S} ℓᵀs. | n/a — restated from Le Guernic and Girard 2010 [21, Def. 1] | `restated` |
| `Def. 3` | (Polytope) P = {s \| Hs ≤ d} = ⟨H, d⟩_H. | n/a — restated from Ziegler [22, Sec. 1.1] | `restated` |
| `Eq. 24` | P ⊖ S = ⟨H, d̃⟩_H, d̃⁽ʲ⁾ = d⁽ʲ⁾ - ρ(S, H⁽ʲ,·⁾ᵀ). | n/a — restated from Kolmanovsky and Gilbert 1998 [23, Thm. 2.2] | `restated` |
| `Def. 4` | (Constrained zonotope) CZ = {c + Σ G⁽·,ⁱ⁾αᵢ \| Σ K⁽·,ⁱ⁾αᵢ = l, αᵢ ∈ [-1, 1]}; without constraints a zonotope. | n/a — restated from [24, Def. 1 and 3]; tracked as `Def. 3` on [Scott et al. 2016](../2016/scott-automatica-constrained-zonotopes.md) | `restated` |
| `Sec. IV-A` | Operation counts: linear map O(hn²), Minkowski difference O(hO(ρ)), Chebyshev center and box by linear programs, the zonotope and constrained-zonotope operations. | n/a — computational complexity, a subject CORALean does not cover | `not-covered` |
| `Alg. 1` | (Inner approximation of the reachable set) Per step: linearize at cen(R̂(t_k)) + ½Δt f(·), compute C, R_aff, R̂_aff, iterate the Lagrange remainder until L ⊆ L̂, then R̂(t_{k+1}) ← R_aff ⊖ R̂_err + 2c (Prop. 1) and R̂(τ_k) ← conv(CZ(R̂(t_k) ⊖ R̂_err ⊖ C), CZ(R̂(t_{k+1}) ⊖ C)) + 2c (Prop. 2), c = cen(C) + cen(R̂_err). | [`InnerMinkDiff.lean`](../../src/CORALean/ContDynamics/NonlinearSys/Operations/InnerMinkDiff.lean), [`InnerMinkDiffLoop.lean`](../../src/CORALean/ContDynamics/NonlinearSys/Operations/InnerMinkDiffLoop.lean), [`InnerMinkDiffStep.lean`](../../src/CORALean/ContDynamics/NonlinearSys/Operations/InnerMinkDiffStep.lean), [`InnerMinkDiffRemainder.lean`](../../src/CORALean/ContDynamics/NonlinearSys/Operations/InnerMinkDiffRemainder.lean), [`InnerMinkDiffOps.lean`](../../src/CORALean/ContDynamics/NonlinearSys/Definitions/InnerMinkDiffOps.lean) — `NonlinearSys.innerMinkDiff`, line by line over exact sets (`CZ` is exact and drops out), the remainder loop of lines 10-13 with fuel and an `Option` result, `cen`, `box`, (6), (9), (13) and (17) supplied as `InnerMinkDiffOps`. [`InnerMinkDiffTimeInterval.lean`](../../src/CORALean/ContDynamics/NonlinearSys/Counterexamples/InnerMinkDiffTimeInterval.lean) — **Counterexample:** `NonlinearSys.innerMinkDiff_timeInterval_counterexample`: one step over [0, 1] of the shear `ẋ = (x₂, 0)` from the box [-1/10, 1/10] × [-1, 1], where C = R̂_err = 0 and c = 0; the output R̂(τ) holds (1/2, 0), which no run reaches at any t ∈ [0, 1]. [`InnerMinkDiffLoopSubsetReachSet.lean`](../../src/CORALean/ContDynamics/NonlinearSys/Theorems/InnerMinkDiffLoopSubsetReachSet.lean), [`InnerMinkDiffStepSubsetReachSet.lean`](../../src/CORALean/ContDynamics/NonlinearSys/Theorems/InnerMinkDiffStepSubsetReachSet.lean), [`ReachSetSubsetReachSetAdd.lean`](../../src/CORALean/ContDynamics/NonlinearSys/Theorems/ReachSetSubsetReachSetAdd.lean), [`InnerMinkDiffLoopAdd.lean`](../../src/CORALean/ContDynamics/NonlinearSys/Theorems/InnerMinkDiffLoopAdd.lean), [`InnerMinkDiffCertOfAbstractionError.lean`](../../src/CORALean/ContDynamics/NonlinearSys/Theorems/InnerMinkDiffCertOfAbstractionError.lean), [`IsInnerMinkDiffCert.lean`](../../src/CORALean/ContDynamics/NonlinearSys/Definitions/IsInnerMinkDiffCert.lean) — `NonlinearSys.innerMinkDiffLoop_subset_reachSet`: every time-point set R̂(t_k) ⊆ R(t_k), by induction over the steps (runs under the constant input concatenate, `NonlinearSys.reachSet_subset_reachSet_add`), given `Prop. 1`'s hypotheses at each step (`IsInnerMinkDiffCert`), R̂_err symmetric about line 14's c among them; `NonlinearSys.IsInnerMinkDiffCert.of_abstractionError` derives (21) from an `AbstractionError` certificate for L̂ on a region the solutions keep to, which stays a hypothesis | `false` — the output R̂(τ) the listing ensures is no inner approximation: line 16 is `Prop. 2`, false for the polytopic X₀ line 1 requires; the time-point sets are inner approximations, line 15 only when cen(C) = 0 (Findings) |
| `Sec. IV-B` | Alg. 1 runs in O((h + n)^{1.5}n³) per step, O(n^{4.5}) for h linear in n. | n/a — computational complexity, a subject CORALean does not cover | `not-covered` |
| `Sec. V` | Benchmarks against the scaling and projection approaches (Table I, Figs. 2-3). | n/a — experiments | `not-a-claim` |

## Findings

**`Prop. 1` — `Lemma 1` needs a convex `A`.** The proof writes x(Δt) = R_con + e^{AΔt}x(0) +
z(x(0)) (21), z continuous with values in R̂_err, and applies `Lemma 1` to A = R_aff(Δt).
`Lemma 1` asks A to be convex, and Prop. 1 asks of X₀ only that it be compact and nonempty, so
for a nonconvex X₀ the lemma does not apply as cited. The proposition is true all the same:
for x ∈ A ⊖ R̂_err the set x + R̂_err lies in A, and a ↦ x + 2c - φ(a) maps it into itself,
so Brouwer's theorem on x + R̂_err, convex and compact because (13) makes R̂_err a zonotope,
gives the fixed point (`minkowskiDiff_subset_of_continuous_of_convex`,
`NonlinearSys.minkowskiDiff_add_subset_reachSet`).
[`MinkowskiDiffAddSubsetReachSet.lean`](../../src/CORALean/ContDynamics/NonlinearSys/Theorems/MinkowskiDiffAddSubsetReachSet.lean)

**`Prop. 2` — false for a nonconvex `X₀`.** The proof writes each state as
x(t) = a + z(x(0), t) with a = x(0) + (t/Δt)(e^{AΔt}x(0) + R_con - x(0)) ∈ conv(X₀, R_aff(Δt))
and then applies `Lemma 1` with A = conv(X₀, R_aff(Δt)). The lemma needs every a ∈ A to come
with an error φ(a); here only the points x(0) + (t/Δt)(R_aff - x(0)) of one x(0) do, and the
hull holds others. For `ẋ = w` with `A = 0` the remainder and the curvature error vanish
((13), and (17) with `F`, `G` and `E(Δt)` sums of powers of `A`), so (23) is
`conv(X₀ ∪ (X₀ + Δt w)) ⊆ R([0, Δt]) = X₀ + [0, Δt] w`. For
`X₀ = ([0, 1/10] ∪ [9/10, 1]) × [0, 1/10]`, `w = (0, 1)`, `Δt = 1`, the midpoint `(1/2, 1/2)` of
`(0, 0)` and `(1, 1)` is in the hull, and every run keeps its first coordinate in
`[0, 1/10] ∪ [9/10, 1]` (`convexHull_timeInterval_counterexample`).
[`ConvexHullTimeInterval.lean`](../../src/CORALean/ContDynamics/NonlinearSys/Counterexamples/ConvexHullTimeInterval.lean)

**`Prop. 2` — false for a convex `X₀` too.** `Alg. 1` passes only polytopes and constrained
zonotopes, so a convex X₀, and convexity does not repair (23): the hull holds points that lie on
no chord `[x(0), R_aff(x(0))]` whenever the flow shears the set, as a linear flow already does.
For the shear `ẋ = (x₂, 0)`, `A = [0 1; 0 0]`, `A² = 0`: the linearization is exact, so
R̂_err = 0 (13); `F(Δt)` is a sum of `Aⁱ`, `i ≥ 2`, and `E(Δt)` of `|A|ⁱ`, `i > η`, so `F = 0`,
and the constant input `w = f(x*) - Ax*` is `0`, so `C = 0` (17); hence `c = 0` and (23) is
`conv(X₀ ∪ e^{AΔt}X₀) ⊆ R([0, Δt])`. For `X₀ = [-1/10, 1/10] × [-1, 1]` and `Δt = 1`,
`e^{A}x₀ = (x₀₁ + x₀₂, x₀₂)`, and `(1/2, 0)`, the midpoint of `(0, -1) ∈ X₀` and
`e^{A}(0, 1) = (1, 1)`, is in the hull; a run through it starts on `x₂ = 0`, where `ẋ = 0`, so
its first coordinate is in `[-1/10, 1/10]` (`convexHull_timeInterval_convex_counterexample`).
The convex correction is therefore no correction, and the row stays `false`: what `Lemma 1`
gives, for each fixed `t` and a convex X₀, is the shrunk image of the convex
`((1 - t/Δt)I + (t/Δt)e^{AΔt})X₀ + (t/Δt)R_con` (where that matrix is invertible), and the union of these over `t` is not the hull. CORA's `linReachInner` computes (23) ([`nonlinearSys` `reachInner`](../coverage/contDynamics/nonlinearSys.md)).
[`ConvexHullTimeIntervalConvex.lean`](../../src/CORALean/ContDynamics/NonlinearSys/Counterexamples/ConvexHullTimeIntervalConvex.lean)

**`Alg. 1` — the output is `Prop. 2`'s.** The listing ensures that R̂(τ) = ⋃_k R̂(τ_k) (line
18) is an inner approximation of the reachable set over [0, t_end], and line 16 computes R̂(τ_k)
by (23). The convex counterexample to `Prop. 2` is an input of the algorithm: for the shear
`ẋ = (x₂, 0)` from the box `X₀ = [-1/10, 1/10] × [-1, 1]`, a polytope as line 1 asks, with
`t_end = 1` and `ω = 1`, line 4 gives `x* = 0` (the box's center is a Chebyshev center), line 5
`w = 0` and `A = [0 1; 0 0]`, line 6 `C = 0`, the remainder loop stops at its first pass with
`L̂ = 0`, so `R̂_err = 0` and `c = 0`, and line 16 is `conv(X₀, e^{A}X₀)`, holding `(1/2, 0)`,
which no run reaches at any `t ∈ [0, 1]` (`NonlinearSys.innerMinkDiff_timeInterval_counterexample`,
the subroutines entering only through what (6), (9), (13), (17) and the center give there).
No correction is known that keeps line 16's hull, so the row is `false`, not `underspecified`.
The time-point sets are sound: by induction over the steps, every R̂(t_k) lies in R(t_k)
(`NonlinearSys.innerMinkDiffLoop_subset_reachSet`), a step from R̂(t_k) reaching only states
some run reaches, since runs under the constant input concatenate
(`NonlinearSys.reachSet_subset_reachSet_add`), given `Prop. 1`'s hypotheses at each step. Of
those, (21) is what the remainder loop certifies: it follows from an `AbstractionError`
certificate for `L̂` on a region the solutions do not leave
(`NonlinearSys.IsInnerMinkDiffCert.of_abstractionError`); the confinement itself, which the box
(25) is meant to give, stays a hypothesis, as in the conservative-linearization rows.
[`InnerMinkDiffTimeInterval.lean`](../../src/CORALean/ContDynamics/NonlinearSys/Counterexamples/InnerMinkDiffTimeInterval.lean),
[`InnerMinkDiffLoopSubsetReachSet.lean`](../../src/CORALean/ContDynamics/NonlinearSys/Theorems/InnerMinkDiffLoopSubsetReachSet.lean)

**`Alg. 1`, line 15 — which center.** `Prop. 1` shifts R_aff ⊖ R̂_err by 2 cen(R̂_err); line 15
shifts it by 2c with c = cen(C) + cen(R̂_err) from line 14, the center `Prop. 2` uses. The two
agree only when C is centered at the origin. CORA's `linReachInner` shifts the time-point set by
nothing (its R̂_err is centered at the origin) and the time-interval sets by 2 cen(C), which is
`Prop. 1` and `Prop. 2` as printed, not line 15. `NonlinearSys.innerMinkDiffLoop_subset_reachSet` takes line 15
as printed and asks R̂_err to be symmetric about line 14's c; a bounded nonempty set has one
center of symmetry, so with cen(R̂_err) that center this is cen(C) = 0, and with `Prop. 1`'s
shift it is `Prop. 1`'s own hypothesis. For a linear field, where R̂_err = 0, line 15 is
R(t_{k+1}) + 2 cen(C), outside R(t_{k+1}) whenever cen(C) ≠ 0, which (17) gives in general
(`F(Δt)` has interval entries `[a, 0]`, `a < 0`); not written in Lean, as the row's class rests
on the time-interval output.
