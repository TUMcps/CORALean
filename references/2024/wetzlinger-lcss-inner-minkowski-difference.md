# Inner Approximations of Reachable Sets for Nonlinear Systems using the Minkowski Difference

```bibtex
@article{wetzlinger2024inner,
  author = {Wetzlinger, M. and Kulmburg, A. and Althoff, M.},
  title = {Inner Approximations of Reachable Sets for Nonlinear Systems using the {Minkowski} Difference},
  journal = {IEEE Control Systems Letters},
  year = {2024}
}
```

**Source:** https://mediatum.ub.tum.de/doc/1749456/1749456.pdf (the accepted author's version on TUM's repository, "accepted for publication in IEEE Control Systems Letters", doi:10.1109/LCSYS.2024.3421194, 6 pages, read in full; text extracted with `pypdf`). Volume and pages from the published record; the typeset article was not reachable. CORA cites the paper in `nonlinearSys/private/priv_reachInnerMinkdiff.m` and `contDynamics/linReachInner.m` without result numbers.  
**Inventory:** confirmed (Definitions 1-4, Lemma 1, Remark 1, Propositions 1-2 and Algorithm 1, each with its own counter; equations (1)-(26), of which the rows below are the displays that make a claim; Table I)

An inner approximation of the reachable set of a nonlinear system computed directly, without an
outer approximation first: the affine part's reachable set minus — Minkowski difference — the
abstraction error's. The time-point step (`Prop. 1`) rests on `Lemma 1`, a fixed-point argument
(Brouwer), and the time-interval step (`Prop. 2`) on `Lemma 1` again; `Alg. 1` runs both with
polytopes and constrained zonotopes. Formalized, on CORALean's own proof of Brouwer's theorem
(`exists_fixedPoint_of_isCompact_convex`): `Lemma 1` as printed, `Prop. 1` from the representation
(21), whose printed proof needs the error set's convexity rather than `R_aff`'s, (21) itself from a
linearization's abstraction-error certificate, so that `Prop. 1` holds for a linearized step, and
`Remark 1`'s counterexample, as is the closed form of the constant-input solution (12).

`Prop. 2` is false, for a nonconvex initial set, which it admits, and for a convex one (a box, under
a linear shear) alike, and holds with the hull replaced by the chords of single initial states, the
Minkowski differences taken at each time, a union over every time and so no computable set. Taken
over the whole chord union, the difference fails, for a convex initial set too, and holds where the
covering start and time can be chosen continuously. Its computable repair is proved: for an initial
set inside a zonotope, (23)'s hull eroded by the ball `B_µ` of the authors' backward-reachability
paper is sound.

`Alg. 1` is written line by line over exact sets; its time-point sets are inner approximations, step
by step, and its output, the union of the time-interval sets, is not, by `Prop. 2`'s convex
counterexample run through the algorithm. With line 16's hull eroded by `B_µ` and line 15 shifted as
`Prop. 1` shifts, every set the algorithm computes is an inner approximation, by induction over the
steps. The rest is restated from the conservative-linearization papers the method is built on.

## Results

| Result | What it says | In CORALean | Class |
|---|---|---|---|
| `Eq. 1` | (Minkowski difference) S₁ ⊖ S₂ := {s \| s ⊕ S₂ ⊆ S₁} = {s \| ∀ s₂ ∈ S₂: s + s₂ ∈ S₁}. | n/a — the standard definition, restated; it is `minkowskiDiff` | `restated` |
| `Eq. 2` | For compact, convex, nonempty S₁, S₂, S₃: S₁ ⊖ (S₂ ⊕ S₃) = (S₁ ⊖ S₂) ⊖ S₃ = (S₁ ⊖ S₃) ⊖ S₂. | n/a — restated from Danilov and Koshevoy 2000 [15, Eq. (2)]; `minkowskiDiff_add_assoc` has it for all sets | `restated` |
| `Eq. 3` | conv(S₁ ⊖ S₃, S₂ ⊖ S₃) ⊆ conv(S₁, S₂) ⊖ S₃. | n/a — restated from [16, Lemma 1]; tracked as `Lemma 1` on [Wetzlinger and Althoff 2026](../2026/wetzlinger-tac-backward-reachability.md) | `restated` |
| `Def. 1` | (Exact reachable set) R(t) := {ξ(t; x(0)) \| x(0) ∈ X₀} for ẋ = f(x), and R(τ) = ⋃_{t∈τ} R(t). | [`ReachSetExact.lean`](../../src/CORALean/ContDynamics/NonlinearSys/Definitions/ReachSetExact.lean) — `NonlinearSys.reachSetExact`, over every solution (the one ξ when f is Lipschitz), with inputs that the autonomous case leaves out; the runs are Carathéodory, the integral equation with a measurable field, so a measurable input is admitted; under a continuous input they are the classical ones (`NonlinearSys.IsTrajectory.hasDerivWithinAt`), so the autonomous ones are the classical ξ | `correct` |
| `Eq. 8` | (6)-(7): f(x) = f(x*) + Df(x*)(x - x*) + l(x), l(x) in the Lagrange remainder L(X), so f(x) ∈ w + A(x - x*) ⊕ L(X). | n/a — restated from [18, Eq. (2)]; tracked as `Eq. 2` on [Althoff et al. 2008](../2008/althoff-cdc-conservative-linearization.md) | `restated` |
| `Eq. 9` | L⁽ⁱ⁾(X) is enclosed by [-l̂⁽ⁱ⁾, l̂⁽ⁱ⁾], l̂⁽ⁱ⁾ = ½ max\|x - x*\|ᵀ max D²f⁽ⁱ⁾ max\|x - x*\|. | n/a — restated from [18, Prop. 1]; tracked as `Prop. 1` on [Althoff et al. 2008](../2008/althoff-cdc-conservative-linearization.md) | `restated` |
| `Eq. 10` | R_aff(Δt) = R_hom(Δt) ⊕ R_con(Δt), R_hom(Δt) = e^{AΔt}X₀ (11), the affine dynamics' solution. | n/a — the variation-of-constants solution, restated; tracked as `Eq. 5` on [Althoff and Krogh 2012](../2012/althoff-hscc-avoiding-intersection.md) | `restated` |
| `Eq. 12` | R_con(Δt) = ∫₀^Δt e^{A(Δt-θ)}dθ w = A⁻¹(e^{AΔt} - I)w; for singular A, A⁻¹ is factored into the series of e^{AΔt}. | [`MulExpIntegral.lean`](../../src/CORALean/ContDynamics/LinearSys/MatExp/Theorems/MulExpIntegral.lean), [`ExpIntegralConstInput.lean`](../../src/CORALean/ContDynamics/LinearSys/Theorems/ExpIntegralConstInput.lean) — the integral is `expIntegral A Δt *ᵥ w` (the series, any A), which is A⁻¹(e^{AΔt} - I) for invertible A | `correct` |
| `Eq. 13` | The abstraction error's reachable set is enclosed by ⊕_{j=0}^η A^jΔt^{j+1}/(j+1)! L ⊕ E(Δt)ΔtL. | n/a — restated from [19], Althoff's thesis (2010); the input solution is the corrected form of `Prop. 2`, tracked as `Prop. 2` on [Althoff, Stursberg, Buss 2007](../2007/althoff-cdc-uncertain-parameters-inputs.md) | `restated` |
| `Eq. 14` | R(Δt) ⊆ R_aff(Δt) ⊕ R̂_err, and (15) R(τ₀) ⊆ R̂_aff(τ₀) ⊕ R̂_err. | n/a — restated from [18, Sec. III] | `restated` |
| `Eq. 16` | R̂_aff(τ₀) = conv(X₀, R_aff(Δt)) ⊕ C encloses the affine time-interval solution, C = F(Δt)X₀ ⊕ G(Δt)w (17). | n/a — restated from [19, Sec. 3.2.2] and [16, Eq. (18), (26)] | `restated` |
| `Lemma 1` | For A ⊂ ℝⁿ nonempty, convex, compact, B centrally symmetric around c, φ: A → B continuous and S = {a + φ(a) \| a ∈ A}: A ⊖ B ⊆ S - 2c (19). | [`MinkowskiDiffSubsetOfContinuous.lean`](../../src/CORALean/ContSet/ContSet/Theorems/MinkowskiDiffSubsetOfContinuous.lean) — `minkowskiDiff_subset_of_continuous`, in any finite-dimensional real normed space, the symmetry as `b ∈ B → 2c - b ∈ B`, by Brouwer's theorem as the paper argues | `correct` |
| `Remark 1` | Continuity of φ cannot be dropped: A = B = [-1, 1] gives A ⊖ B = {0}, and φ = sign (sign 0 = 1) gives S = [-2, -1) ∪ [1, 2]. | [`MinkowskiDiffNotSubsetOfDiscontinuous.lean`](../../src/CORALean/ContSet/ContSet/Theorems/MinkowskiDiffNotSubsetOfDiscontinuous.lean) — all three sets as stated, and 0 ∉ S | `correct` |
| `Prop. 1` | (Time-point reachable set) For X₀ compact, nonempty and R̂_err centrally symmetric, R̂(Δt) = R_aff(Δt) ⊖ R̂_err + 2c ⊆ R(Δt), c = cen(R̂_err) (20). | [`MinkowskiDiffAddSubsetReachSetExact.lean`](../../src/CORALean/ContDynamics/NonlinearSys/Theorems/MinkowskiDiffAddSubsetReachSetExact.lean), [`MinkowskiDiffSubsetOfContinuousOfConvex.lean`](../../src/CORALean/ContSet/ContSet/Theorems/MinkowskiDiffSubsetOfContinuousOfConvex.lean), [`SubMemInputSolution.lean`](../../src/CORALean/ContDynamics/NonlinearSys/Theorems/SubMemInputSolution.lean), [`MinkowskiDiffInputSolutionSubsetReachSetExact.lean`](../../src/CORALean/ContDynamics/NonlinearSys/Theorems/MinkowskiDiffInputSolutionSubsetReachSetExact.lean) — `NonlinearSys.minkowskiDiff_add_subset_reachSetExact`: e^{AΔt} = `M` invertible, R_con = `v`, R̂_err a convex compact set as (13) makes it. The files of the second link are described in the Findings. | `proof-gap` — the proof applies `Lemma 1` with A = R_aff(Δt) = e^{AΔt}X₀ + R_con, which is not convex for the merely compact X₀ the proposition allows; the statement holds because R̂_err is (Findings) |
| `Prop. 2` | (Time-interval reachable set) For a compact, non-empty X₀ and E = C ⊕ R̂_err (22) centrally symmetric around c, R̂(τ₀) = conv((X₀ ⊖ C) ⊖ R̂_err, R̂(Δt) ⊖ C) + 2c ⊆ R(τ₀) (23). | [`ConvexHullTimeInterval.lean`](../../src/CORALean/ContDynamics/NonlinearSys/Counterexamples/ConvexHullTimeInterval.lean), [`ConvexHullTimeIntervalConvex.lean`](../../src/CORALean/ContDynamics/NonlinearSys/Counterexamples/ConvexHullTimeIntervalConvex.lean), [`MinkowskiDiffChordSubsetReachSetExact.lean`](../../src/CORALean/ContDynamics/NonlinearSys/Theorems/MinkowskiDiffChordSubsetReachSetExact.lean), [`NotMemMinkowskiDiffChordShear.lean`](../../src/CORALean/ContDynamics/NonlinearSys/Theorems/NotMemMinkowskiDiffChordShear.lean), [`MinkowskiDiffIUnionChord.lean`](../../src/CORALean/ContDynamics/NonlinearSys/Counterexamples/MinkowskiDiffIUnionChord.lean), [`MinkowskiDiffIUnionChordConvex.lean`](../../src/CORALean/ContDynamics/NonlinearSys/Counterexamples/MinkowskiDiffIUnionChordConvex.lean), [`AddMemReachSetExactOfChordSection.lean`](../../src/CORALean/ContDynamics/NonlinearSys/Theorems/AddMemReachSetExactOfChordSection.lean), [`MinkowskiDiffConvexHullBallSubsetReachSetExact.lean`](../../src/CORALean/ContDynamics/NonlinearSys/Theorems/MinkowskiDiffConvexHullBallSubsetReachSetExact.lean) — **Counterexample:** `convexHull_timeInterval_counterexample`, `convexHull_timeInterval_convex_counterexample`: (23) holds a point no run reaches. The files are described in the Findings. | `fixed` — false for a nonconvex X₀, which the proposition admits, and for a convex one, all that `Alg. 1` passes; true for an X₀ inside a zonotope once the hull is eroded by the ball B_µ of [16], µ = √γ‖(e^{AΔt} - I)G‖₂, a computable set. The chords of single initial states with the Minkowski differences taken at each t are sound too, but no computable set, and ⊖ over the whole chord union is false, for a convex X₀ as well (Findings) |
| `Def. 2` | (Support function) ρ(S, ℓ) := max_{s∈S} ℓᵀs. | n/a — restated from Le Guernic and Girard 2010 [21, Def. 1] | `restated` |
| `Def. 3` | (Polytope) P = {s \| Hs ≤ d} = ⟨H, d⟩_H. | n/a — restated from Ziegler [22, Sec. 1.1] | `restated` |
| `Eq. 24` | P ⊖ S = ⟨H, d̃⟩_H, d̃⁽ʲ⁾ = d⁽ʲ⁾ - ρ(S, H⁽ʲ,·⁾ᵀ). | n/a — restated from Kolmanovsky and Gilbert 1998 [23, Thm. 2.2] | `restated` |
| `Def. 4` | (Constrained zonotope) CZ = {c + Σ G⁽·,ⁱ⁾αᵢ \| Σ K⁽·,ⁱ⁾αᵢ = l, αᵢ ∈ [-1, 1]}; without constraints a zonotope. | n/a — restated from [24, Def. 1 and 3]; tracked as `Def. 3` on [Scott et al. 2016](../2016/scott-automatica-constrained-zonotopes.md) | `restated` |
| `Sec. IV-A` | Operation counts: linear map O(hn²), Minkowski difference O(hO(ρ)), Chebyshev center and box by linear programs, the zonotope and constrained-zonotope operations. | n/a — computational complexity, a subject CORALean does not cover | `not-covered` |
| `Alg. 1` | (Inner approximation of the reachable set) Per step: linearize at cen(R̂(t_k)) + ½Δt f(·), compute C, R_aff, R̂_aff, iterate the Lagrange remainder until L ⊆ L̂, then R̂(t_{k+1}) ← R_aff ⊖ R̂_err + 2c (Prop. 1) and R̂(τ_k) ← conv(CZ(R̂(t_k) ⊖ R̂_err ⊖ C), CZ(R̂(t_{k+1}) ⊖ C)) + 2c (Prop. 2), c = cen(C) + cen(R̂_err). | [`InnerMinkDiff.lean`](../../src/CORALean/ContDynamics/NonlinearSys/Operations/InnerMinkDiff.lean), [`InnerMinkDiffLoop.lean`](../../src/CORALean/ContDynamics/NonlinearSys/Operations/InnerMinkDiffLoop.lean), [`InnerMinkDiffStep.lean`](../../src/CORALean/ContDynamics/NonlinearSys/Operations/InnerMinkDiffStep.lean), [`InnerMinkDiffRemainder.lean`](../../src/CORALean/ContDynamics/NonlinearSys/Operations/InnerMinkDiffRemainder.lean), [`InnerMinkDiffOps.lean`](../../src/CORALean/ContDynamics/NonlinearSys/Definitions/InnerMinkDiffOps.lean), [`InnerMinkDiffTimeInterval.lean`](../../src/CORALean/ContDynamics/NonlinearSys/Counterexamples/InnerMinkDiffTimeInterval.lean), [`InnerMinkDiffLoopSubsetReachSetExact.lean`](../../src/CORALean/ContDynamics/NonlinearSys/Theorems/InnerMinkDiffLoopSubsetReachSetExact.lean), [`InnerMinkDiffStepSubsetReachSetExact.lean`](../../src/CORALean/ContDynamics/NonlinearSys/Theorems/InnerMinkDiffStepSubsetReachSetExact.lean), [`ReachSetExactSubsetReachSetExactAdd.lean`](../../src/CORALean/ContDynamics/NonlinearSys/Theorems/ReachSetExactSubsetReachSetExactAdd.lean), [`InnerMinkDiffLoopAdd.lean`](../../src/CORALean/ContDynamics/NonlinearSys/Theorems/InnerMinkDiffLoopAdd.lean), [`InnerMinkDiffCertOfAbstractionError.lean`](../../src/CORALean/ContDynamics/NonlinearSys/Theorems/InnerMinkDiffCertOfAbstractionError.lean), [`IsInnerMinkDiffCert.lean`](../../src/CORALean/ContDynamics/NonlinearSys/Definitions/IsInnerMinkDiffCert.lean), [`InnerMinkDiffCorrected.lean`](../../src/CORALean/ContDynamics/NonlinearSys/Operations/InnerMinkDiffCorrected.lean), [`InnerMinkDiffCorrectedLoop.lean`](../../src/CORALean/ContDynamics/NonlinearSys/Operations/InnerMinkDiffCorrectedLoop.lean), [`InnerMinkDiffCorrectedStep.lean`](../../src/CORALean/ContDynamics/NonlinearSys/Operations/InnerMinkDiffCorrectedStep.lean), [`IsInnerMinkDiffCorrectedCert.lean`](../../src/CORALean/ContDynamics/NonlinearSys/Definitions/IsInnerMinkDiffCorrectedCert.lean), [`InnerMinkDiffCorrectedStepSubsetReachSetExact.lean`](../../src/CORALean/ContDynamics/NonlinearSys/Theorems/InnerMinkDiffCorrectedStepSubsetReachSetExact.lean), [`InnerMinkDiffCorrectedLoopSubsetReachSetExact.lean`](../../src/CORALean/ContDynamics/NonlinearSys/Theorems/InnerMinkDiffCorrectedLoopSubsetReachSetExact.lean), [`InnerMinkDiffCorrectedSubsetReachSetExact.lean`](../../src/CORALean/ContDynamics/NonlinearSys/Theorems/InnerMinkDiffCorrectedSubsetReachSetExact.lean), [`InnerMinkDiffCorrectedInstance.lean`](../../src/CORALean/Examples/InnerMinkDiffCorrectedInstance.lean), [`InnerMinkDiffStepCenter.lean`](../../src/CORALean/ContDynamics/NonlinearSys/Counterexamples/InnerMinkDiffStepCenter.lean) — **Counterexample:** `NonlinearSys.innerMinkDiff_timeInterval_counterexample` | `underspecified` — the output R̂(τ) the listing ensures is no inner approximation as printed: line 16 is `Prop. 2`, false for the polytopic X₀ line 1 requires, and line 15 shifts by 2c, unsound once cen(C) ≠ 0. A correction of a listing is `underspecified` (README): with line 16's hull eroded by B_µ and line 15 shifted by 2 cen(R̂_err), every set it computes is an inner approximation (Findings) |
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
`NonlinearSys.minkowskiDiff_add_subset_reachSetExact`).
[`MinkowskiDiffAddSubsetReachSetExact.lean`](../../src/CORALean/ContDynamics/NonlinearSys/Theorems/MinkowskiDiffAddSubsetReachSetExact.lean)

**`Prop. 2` — false for a nonconvex `X₀`.** The proof writes each state as
x(t) = a + z(x(0), t) with a = x(0) + (t/Δt)(e^{AΔt}x(0) + R_con - x(0)) ∈ conv(X₀, R_aff(Δt))
and then applies `Lemma 1` with A = conv(X₀, R_aff(Δt)). The lemma needs every a ∈ A to come
with an error φ(a); here only the points x(0) + (t/Δt)(R_aff - x(0)) of one x(0) do, and the
hull holds others. For `ẋ = w` with `A = 0` the remainder and the curvature error vanish
((13), and (17) with `F`, `G` and `E(Δt)` sums of powers of `A`; derived in Lean from the
definitions, at every Taylor order and every `x*`), so (23) is
`conv(X₀ ∪ (X₀ + Δt w)) ⊆ R([0, Δt]) = X₀ + [0, Δt] w`. For
`X₀ = ([0, 1/10] ∪ [9/10, 1]) × [0, 1/10]`, `w = (0, 1)`, `Δt = 1`, the midpoint `(1/2, 1/2)` of
`(0, 0)` and `(1, 1)` is in the hull, and every run keeps its first coordinate in
`[0, 1/10] ∪ [9/10, 1]` (`convexHull_timeInterval_counterexample`).
[`ConvexHullTimeInterval.lean`](../../src/CORALean/ContDynamics/NonlinearSys/Counterexamples/ConvexHullTimeInterval.lean)

**`Prop. 2` — false for a convex `X₀` too.** `Alg. 1` passes only polytopes and constrained zonotopes,
so a convex X₀, and convexity does not repair (23): the hull holds points that lie on no chord
`[x(0), R_aff(x(0))]` whenever the flow shears the set, as a linear flow already does. For the shear
`ẋ = (x₂, 0)`, `A = [0 1; 0 0]`, `A² = 0`, so `e^{A} = I + A`: the linearization is exact, so
`D²f ≡ 0`, L̂ = 0 (9) and R̂_err = 0 (13). For a Taylor order `η ≥ 1`, `E(Δt)` of [16, (19)] is
`e^{|A|Δt} - Σ_{i≤η} (|A|Δt)ⁱ/i! = 0`, `|A| = A`, and `F(Δt)` of [16, (18)] a sum of `Aⁱ`, `i ≥ 2`,
and `E`, so `F = 0`; the constant input `w = f(x*) - Ax*` is `0`, so `C = 0` (17) though `G ≠ 0`;
hence `c = 0` and (23) is `conv(X₀ ∪ e^{AΔt}X₀) ⊆ R([0, Δt])`. At `η = 0`, `E = |A|Δt` and
`C = [-1, 1] × {0}`, wider than the box below and its shear, so both Minkowski differences are empty
and (23) holds. For `X₀ = [-1/10, 1/10] × [-1, 1]` and `Δt = 1`, `e^{A}x₀ = (x₀₁ + x₀₂, x₀₂)`, and
`(1/2, 0)`, the midpoint of `(0, -1) ∈ X₀` and `e^{A}(0, 1) = (1, 1)`, is in the hull; a run through
it starts on `x₂ = 0`, where `ẋ = 0`, so its first coordinate is in `[-1/10, 1/10]`
(`convexHull_timeInterval_convex_counterexample`, with every term of (23) computed and the vanishing
ones derived). Convexity is therefore no correction.

**`Prop. 2` — the per-slice repair.** What `Lemma 1` gives, for each fixed `t` and a convex X₀, is
the shrunk image of the convex chord slice `((1 - t/Δt)I + (t/Δt)e^{AΔt})X₀ + (t/Δt)R_con` (where
that matrix is invertible), and the union of these over `t` is not the hull. That repair is proved,
but it is no computable set: `⋃_{t∈[0,Δt]} ((slice(t) ⊖ C) ⊖ R̂_err) + 2c ⊆ R(τ₀)`, each slice being
`Prop. 1` at time `t` with that matrix, `⊖ C`, `⊖ R̂_err` and the `2c` shift all slice-wise, given
that every solution lies within `E = C ⊕ R̂_err` of its chord, the representation the printed proof
writes (`NonlinearSys.minkowskiDiff_chord_subset_reachSetExact`). For the shear the slices are
`(I + tA)X₀ = R(t)`, so the repaired set is `R([0, 1])` and drops `(1/2, 0)`
(`NonlinearSys.not_mem_minkowskiDiff_chord_shear`).

**`Prop. 2` — the whole-chord-union failure.** `⊖` of the whole chord union (the dependent
`linComb`), nonconvex and larger than the union of slice differences, is no repair. Under the same
hypotheses it fails for `ẋ = (1/2, 0)`, `Δt = 1`, the connected `Π`-shaped
`X₀ = [0, 1] × [0, 3] ∪ [2, 3] × [0, 3] ∪ [0, 3] × [2, 3]` and chords `x₀ + t(1, 0)`, `E` the
segment from `(-1/2, 0)` to `0`, `c = (-1/4, 0)`. The chords sweep `[0, 4] × [0, 3]`, the runs leave
the strip `(3/2, 2) × [0, 2)` between the legs empty, and the eroded union holds `(7/4, 1)`
(`NonlinearSys.minkowskiDiff_iUnion_chord_counterexample`). Such chords are what linearizing at
`cen(X₀) + (Δt/2) f = (7/4, 3/2)` gives, a point of that strip where the field may differ from its
value on the runs. What fails is the covering time: `(7/4, 1) + E` is covered by the left leg near
`t = 1` and by the right leg at `t = 0`, and Brouwer's theorem, the proof's tool, needs one
continuous choice. With it the union-level set is sound:
`NonlinearSys.add_mem_reachSetExact_of_chord_section` proves `z + 2c ∈ R(τ₀)` whenever the chords
cover `z + E` through a start `x₀ ∈ X₀` and time `t` chosen continuously in the point, Brouwer on
`z + E` and Grönwall's continuity of `(x₀, t) ↦ x(t)`; a constant time is the per-slice repair.

**`Prop. 2` — the three-dimensional convex counterexample.** A convex X₀, all `Alg. 1` passes, does
not save it: for `ẋ = (x₃, 1, 0)`, `Δt = 1`, the box `X₀ = [-1/2, -1/4] × [-1, 0] × [-1, 1]`,
`M = e^{A} = I + e₁e₃ᵀ`, `v = (-1/2, 0, -1)`, `E` the segment from `0` to `δ = (1/2, 1, 1)` and
`c = δ/2`, every run is its chord plus `tδ`. `-λδ` lies in `X₀` for `λ ≥ 1/2` and on the chord of
`(λ/2 - 1/2, -λ, 1 - λ)` at `t = 1` for `λ ≤ 1/2`, so the eroded union holds `-δ + 2c = 0`, while a
run through `0` would start at `(0, -t, 0)`, outside `X₀`
(`NonlinearSys.minkowskiDiff_iUnion_chord_convex_counterexample`). The covering time again jumps,
from `0` to `1`, and the start-time fibres `{t | y on the chord of some x₀ ∈ X₀ at t}` are
disconnected. The earlier random search, over 2-D linear fields only (about 2500 instances), had
found no such point; whether a planar convex instance exists is not settled.

**`Prop. 2` — the computable repair with the ball `B_µ`.** The convex
`conv((X₀ ⊖ C) ⊖ R̂_err, R̂(Δt) ⊖ C) ⊖ B_μ + 2c`, `μ = √γ‖(e^{AΔt} - I)G‖₂`, was to rest on [16,
(20)] (arXiv v3's (21)), which cites [15, Prop. 1], an outer Hausdorff bound whose proof alone uses
the inner inclusion (see [Wetzlinger et al.
2023](../2023/wetzlinger-fully-automated-verification.md)). That inclusion is false: [16, (20)]
erodes by `F H(t_k)` where the trajectories need `-F H(t_k)`, and for `ẋ = (x₂, x₃, 0)` its set
holds a point no run reaches (`LinearSys.convexHull_minkowskiDiff_ball_counterexample`, on
[Wetzlinger and Althoff 2026](../2026/wetzlinger-tac-backward-reachability.md)). The candidate does
not fall with it: for `C` centrally symmetric about `c`, `(S ⊖ C) + 2c = S ⊖ (-C)`, so its `+ 2c`
erodes on the side the trajectories need, and that witness is not in it. It is sound, and it is the
computable repair that makes the row `fixed`: for a convex X₀ inside a zonotope `⟨c₀, G⟩` with `γ`
generators, `conv(((X₀ ⊖ C) ⊖ R̂_err) ∪ ((R_aff ⊖ R̂_err) ⊖ C)) ⊖ B_µ + 2c ⊆ R(τ₀)`,
`µ = √γ‖(e^{AΔt} - I)G‖₂`, given that every solution lies within `E` of its chord
(`NonlinearSys.minkowskiDiff_convexHull_ball_subset_reachSetExact`; (13) makes `R̂_err` symmetric
about `0`, so `R̂(Δt)`'s own shift vanishes).

**`Prop. 2` — the proof of the margin.** The `B_µ` margin is twice what is used: a hull point
`p = θa + (1 - θ)k`, `a ∈ X₀ ⊖ E`, `k ∈ R_aff ⊖ E`, moved by `e ∈ E`, is
`θa₁ + (1 - θ)(e^{AΔt}a₂ + R_con)` with `a₁ = a + e` and `a₂ = e^{-AΔt}(k + e - R_con)` in X₀, and
lies `θ(1 - θ)(e^{AΔt} - I)(a₂ - a₁)`, at most `µ/2` in `‖·‖₂`, from the chord of `θa₁ + (1 - θ)a₂`
at `t = (1 - θ)Δt`. Brouwer's theorem on `B_µ(y) × E`, for `y` in the eroded hull, finds `p` and `e`
with `p` minus that deviation equal to `y` and `e = 2c - φ`, `φ` the run's deviation from its chord,
so that run is at `y + 2c`. A continuous choice of `θ`, `a`, `k` is not needed, a representation
interpolated over a finite net of the ball (weights `θ`, `θa`, `(1 - θ)k` mix convexly) being within
the other `µ/2`.

**`Prop. 2` — the random search and CORA.** The earlier random search (linear fields, 2-D and 3-D,
about 850 nonempty instances) and one over 3-D shears with chords off the exact flow found no
failure, as the proof says. CORA's `linReachInner` computes (23) ([`nonlinearSys`
`reachInner`](../coverage/contDynamics/nonlinearSys.md)).
[`ConvexHullTimeIntervalConvex.lean`](../../src/CORALean/ContDynamics/NonlinearSys/Counterexamples/ConvexHullTimeIntervalConvex.lean)

**`Alg. 1` — the output is `Prop. 2`'s.** The listing ensures that R̂(τ) = ⋃_k R̂(τ_k) (line 18) is an
inner approximation of the reachable set over [0, t_end], and line 16 computes R̂(τ_k) by (23). The
convex counterexample to `Prop. 2` is an input of the algorithm. Take the shear `ẋ = (x₂, 0)` from
the box `X₀ = [-1/10, 1/10] × [-1, 1]`, a polytope as line 1 asks, with `t_end = 1` and `ω = 1`.
Line 4 gives `x* = 0` (the box's center is a Chebyshev center), line 5 `w = 0` and `A = [0 1; 0 0]`,
line 6 `C = 0`. The remainder loop stops at its first pass with `L̂ = 0`, so `R̂_err = 0` and
`c = 0`. Line 16 is `conv(X₀, e^{A}X₀)`, holding `(1/2, 0)`, which no run reaches at any
`t ∈ [0, 1]` (`NonlinearSys.innerMinkDiff_timeInterval_counterexample`, for every `η ≥ 1`). Formulas
(9), (13) and (17), with `F`, `G`, `E` of [16, (18), (19), (26)], are the printed formulas and their
values are derived. The center, the box, the Jacobian (6) and the interval operations of lines 9-13
enter as hypotheses.

**`Alg. 1` — the corrected listing.** Line 16 with its hull eroded by `B_µ`, `µ` from the generator
matrix of `R̂(t_k)`, is sound: `R̂(t_k)` is a constrained zonotope inside the zonotope of its own
generators, which is what `NonlinearSys.minkowskiDiff_convexHull_ball_subset_reachSetExact` asks.
The corrected listing, `NonlinearSys.innerMinkDiffCorrected`, computes it, and with it line 15 by
`Prop. 1`'s shift `2 cen(R̂_err)`: the repaired hull erodes `(R_aff ⊖ R̂_err) ⊖ C`, so the
`R̂(t_{k+1})` line 16 reads must carry no other shift, and line 15's `2c` is unsound on its own
(below).

**`Alg. 1` — soundness of the corrected listing.** Both steps are exact or inner given the step's
hypotheses: `Prop. 1` and the repaired `Prop. 2` are inclusions in the exact reachable set, `⊖`,
`conv` and the shifts are taken exactly, and `CZ` converts exactly [1, Sec. IV-A]. The convexity the
hull erosion needs propagates (`R_aff` is an affine image of a convex `R̂(t_k)`, and `⊖` keeps
convexity), and `R̂_err` symmetric about `0`, as (13) makes it, and about `cen(R̂_err)` gives
`cen(R̂_err) = 0`, a bounded set surviving no translation. By induction over the steps,
`R̂(t_k) ⊆ R(t_k)`, `R̂(τ_k) ⊆ R(τ_k)` and the output lies in `R([0, t_end])`
(`NonlinearSys.innerMinkDiffCorrectedLoop_subset_reachSetExact`,
`NonlinearSys.innerMinkDiffCorrected_subset_reachSetExact`), given at every step of the run the
hypotheses of `Prop. 1` and `Prop. 2` (`IsInnerMinkDiffCorrectedCert`); on `ẋ = 0` from `[0, 1]`
they hold and the output is nonempty (`Examples/InnerMinkDiffCorrectedInstance.lean`). A listing
corrected is `underspecified` (README).

**`Alg. 1` — the finite union of slices.** The per-slice repair of `Prop. 2` is a union over every
`t ∈ [0, Δt]`, no set line 16 can compute; a finite union of its slices is computable and sound, but
covers only the chosen times.

**`Alg. 1` — the time-point sets as printed.** The time-point sets are sound: by induction over the
steps, every R̂(t_k) lies in R(t_k) (`NonlinearSys.innerMinkDiffLoop_subset_reachSetExact`), a step
from R̂(t_k) reaching only states some run reaches, since runs under the constant input concatenate
(`NonlinearSys.reachSetExact_subset_reachSetExact_add`), given `Prop. 1`'s hypotheses at each step.
Of those, (21) is what the remainder loop certifies: it follows from an `IsAbstractionError`
certificate for `L̂` on a region the solutions do not leave
(`NonlinearSys.IsInnerMinkDiffCert.of_abstractionError`); the confinement itself, which the box (25)
is meant to give, stays a hypothesis, as in the conservative-linearization rows.
[`InnerMinkDiffTimeInterval.lean`](../../src/CORALean/ContDynamics/NonlinearSys/Counterexamples/InnerMinkDiffTimeInterval.lean),
[`InnerMinkDiffLoopSubsetReachSetExact.lean`](../../src/CORALean/ContDynamics/NonlinearSys/Theorems/InnerMinkDiffLoopSubsetReachSetExact.lean)

**`Alg. 1`, line 15 — which center.** `Prop. 1` shifts R_aff ⊖ R̂_err by 2 cen(R̂_err); line 15
shifts it by 2c with c = cen(C) + cen(R̂_err) from line 14, the center `Prop. 2` uses. The two agree
only when C is centered at the origin. CORA's `linReachInner` shifts the time-point set by nothing
(its R̂_err is centered at the origin) and the time-interval sets by 2 cen(C), which is `Prop. 1`
and `Prop. 2` as printed, not line 15. `NonlinearSys.innerMinkDiffLoop_subset_reachSetExact` takes
line 15 as printed and asks R̂_err to be symmetric about line 14's c; a bounded nonempty set has one
center of symmetry, so with cen(R̂_err) that center this is cen(C) = 0, and with `Prop. 1`'s shift
it is `Prop. 1`'s own hypothesis. For a linear field, where R̂_err = 0, line 15 is R(t_{k+1}) + 2
cen(C), outside R(t_{k+1}) whenever cen(C) ≠ 0, which (17) gives in general (`F(Δt)` has interval
entries `[a, 0]`, `a < 0`).

****`Alg. 1`, line 15 — the Lean counterexample.**.**
`NonlinearSys.innerMinkDiffStep_center_counterexample`
([`InnerMinkDiffStepCenter.lean`](../../src/CORALean/ContDynamics/NonlinearSys/Counterexamples/InnerMinkDiffStepCenter.lean))
is this for `ẋ = (x₂, 1)` from `[-1/10, 1/10]²`, where (17) gives `C = [-1/8, 0] × {0}`, derived
from `innerCurvatureError` and centered at `(-1/16, 0)`: line 15 holds `(3/8, 1)`, which no run
reaches at `t = 1`. `NonlinearSys.innerMinkDiffStep_center_counterexample_instance` states it with
no hypothesis, at the subroutines `shearDriftOps 1` (the interval hull as box, its midpoint as
center, and the tree's own (17), (13) and (9)). The corrected listing shifts line 15 by
`2 cen(R̂_err)`, which is `0`.

**`Alg. 1` — what the linked files state.**

* `NonlinearSys.innerMinkDiff`, line by line over exact sets (`CZ` is exact and drops out), the
  remainder loop of lines 10-13 with fuel and an `Option` result, `cen`, `box`, (6), (9), (13) and
  (17) supplied as `InnerMinkDiffOps`.
* `NonlinearSys.innerMinkDiff_timeInterval_counterexample`: one step over [0, 1] of the shear
  `ẋ = (x₂, 0)` from the box [-1/10, 1/10] × [-1, 1], where C = R̂_err = 0 and c = 0. The output R̂(τ)
  holds (1/2, 0), which no run reaches at any t ∈ [0, 1].
* `NonlinearSys.innerMinkDiffLoop_subset_reachSetExact`: every time-point set R̂(t_k) ⊆ R(t_k), by
  induction over the steps (runs under the constant input concatenate,
  `NonlinearSys.reachSetExact_subset_reachSetExact_add`), given `Prop. 1`'s hypotheses at each step
  (`IsInnerMinkDiffCert`), R̂_err symmetric about line 14's c among them.
* `NonlinearSys.IsInnerMinkDiffCert.of_abstractionError` derives (21) from an `IsAbstractionError`
  certificate for L̂ on a region the solutions keep to, which stays a hypothesis.
* The corrected listing, `NonlinearSys.innerMinkDiffCorrected`: line 16's hull eroded by B_µ, µ =
  √h‖(e^{AΔt} - I)G‖₂, G the h generators of R̂(t_k) (a supplied `zono`), and line 15 shifted by
  `Prop. 1`'s 2 cen(R̂_err).
* `NonlinearSys.innerMinkDiffCorrectedStep_subset_reachSetExact` (line 15 by `Prop. 1`, line 16 by
  the repaired `Prop. 2`, R̂(t_{k+1}) convex again),
  `NonlinearSys.innerMinkDiffCorrectedLoop_subset_reachSetExact` (by induction from a convex X₀:
  R̂(t_k) ⊆ R(t_k), R̂(τ_k) ⊆ R(τ_k) and the union so far in R([0, t_k])) and
  `NonlinearSys.innerMinkDiffCorrected_subset_reachSetExact` (the output in R([0, t_end])). Each step's hypotheses are a certificate on the run (`IsInnerMinkDiffCorrectedCert`: R̂_err symmetric about 0
  and cen(R̂_err), E = C ⊕ R̂_err symmetric about c, R̂(t_k) inside `zono`'s zonotope, (21) and the
  chord representation (22)).
* The certificates hold for ẋ = 0 from [0, 1], and the output is nonempty.
* `NonlinearSys.innerMinkDiffStep_center_counterexample`: line 15 of one step, `Δt = 1`, of the
  affine `ẋ = (x₂, 1)` from the box `[-1/10, 1/10]²` holds `(3/8, 1)`, which no run reaches at
  `t = 1`, for any Taylor order `η ≥ 1`, with (17) derived from `innerCurvatureError`.
* `NonlinearSys.innerMinkDiffStep_center_counterexample_instance`: the same at the concrete
  subroutines `shearDriftOps 1`, with no hypothesis and one pass of the remainder loop.

**`Prop. 2` — what the linked files state.**

* `convexHull_timeInterval_counterexample`: for `ẋ = (0, 1)` and two squares as X₀, (23) in full at
  every Taylor order η, η = 0 included, and every center x* of line 4 (cen(X₀) has no formula), its
  terms computed from (6), (9), (12), (13), (17) and line 14: C = R̂_err = {0}, L̂ = 0, c = 0 and
  R_con = Δt w derived (A = 0), though w ≠ 0. (23) holds a point no run reaches.
* `convexHull_timeInterval_convex_counterexample`: the same for the shear `ẋ = (x₂, 0)` from the box
  X₀ = [-1/10, 1/10] × [-1, 1], (23) in full at every Taylor order η ≥ 1 and cen(X₀) = 0, its terms
  computed from (6), (9), (12), (13), (17) and line 14, and C = R̂_err = {0}, L̂ = 0, c = 0 derived
  (`A² = 0`).
* The repair: `NonlinearSys.minkowskiDiff_chord_subset_reachSetExact`, ⋃_{t∈[0,Δt]} ((chords(t) ⊖ C)
  ⊖ R̂_err) + 2c ⊆ R(τ₀), chords(t) = {x₀ + (t/Δt)(e^{AΔt}x₀ + R_con - x₀) | x₀ ∈ X₀}, each slice
  `Prop. 1` at time t with (1 - t/Δt)I + (t/Δt)e^{AΔt} invertible, the solutions' representation by
  chord plus E a hypothesis as (21) is for `Prop. 1`.
* `NonlinearSys.not_mem_minkowskiDiff_chord_shear`: the repaired set of the shear no longer holds
  (1/2, 0).
* `NonlinearSys.minkowskiDiff_iUnion_chord_counterexample`: the repair with ⊖ C ⊖ R̂_err taken over
  the whole chord union instead, under the same hypotheses, is false, for ẋ = (1/2, 0), the connected
  Π-shaped X₀ = [0, 1] × [0, 3] ∪ [2, 3] × [0, 3] ∪ [0, 3] × [2, 3] and chords x₀ + t(1, 0).
* `NonlinearSys.minkowskiDiff_iUnion_chord_convex_counterexample`: the same for a convex X₀, ẋ =
  (x₃, 1, 0), the box X₀ = [-1/2, -1/4] × [-1, 0] × [-1, 1] and chords x₀ + t(x₀₃ - 1/2, 0, -1).
* `NonlinearSys.add_mem_reachSetExact_of_chord_section`: that union-level set is sound at every
  point z + 2c whose z + E the chords cover through a start and time chosen continuously.
* The computable repair, `NonlinearSys.minkowskiDiff_convexHull_ball_subset_reachSetExact`:
  conv(((X₀ ⊖ C) ⊖ R̂_err) ∪ ((R_aff ⊖ R̂_err) ⊖ C)) ⊖ B_µ + 2c ⊆ R(τ₀), B_µ the Euclidean ball of [16, (21)], µ = √γ‖(e^{AΔt} - I)G‖₂. It holds for a convex X₀ inside a zonotope ⟨c₀, G⟩ with γ generators (a zonotope or a constrained zonotope). R̂(Δt)'s shift 2 cen(R̂_err) is 0 as (13) makes R̂_err symmetric about 0, and the solutions' representation by chord plus E is a hypothesis as for the per-slice repair.

**`Prop. 1` — what the linked files state.**

* The proof's representation (21) is the hypothesis `herr` (restated from [18], like (14)), the
  solutions and the field's Lipschitz constant along them (the paper's standing assumption) are
  hypotheses, and Grönwall gives the continuity of `z` the proof invokes.
* `minkowskiDiff_subset_of_continuous_of_convex` is `Lemma 1` with `B`, not `A`, convex.
* (21) derived from a linearization: `NonlinearSys.IsTrajectory.sub_mem_inputSolution` for a run
  that stays in the region of an `IsAbstractionError` certificate `L`, with R̂_err =
  `inputSolution Δt η L` (13), and with it
  `NonlinearSys.minkowskiDiff_inputSolution_subset_reachSetExact`, the proposition for a linearized
  step, the confinement still a hypothesis.

## Cited without a result

These name the paper as a whole. A locator would put each in a row above.

* [`ExpRemainderMatShear.lean`](../../src/CORALean/ContDynamics/NonlinearSys/Theorems/ExpRemainderMatShear.lean)
* [`InnerAbstrErrShear.lean`](../../src/CORALean/ContDynamics/NonlinearSys/Theorems/InnerAbstrErrShear.lean)
* [`InnerCurvatureErrorShear.lean`](../../src/CORALean/ContDynamics/NonlinearSys/Theorems/InnerCurvatureErrorShear.lean)
