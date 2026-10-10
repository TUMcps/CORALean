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
`R_aff`'s, and `Remark 1`'s counterexample, as is the closed form of the constant-input
solution (12). `Prop. 2` is open. The rest is restated from the conservative-linearization
papers the method is built on.

## Results

| Result | What it says | In CORALean | Class |
|---|---|---|---|
| `Eq. 1` | (Minkowski difference) S₁ ⊖ S₂ := {s \| s ⊕ S₂ ⊆ S₁} = {s \| ∀ s₂ ∈ S₂: s + s₂ ∈ S₁}. | n/a — the standard definition, restated; it is `minkowskiDiff` | `restated` |
| `Eq. 2` | For compact, convex, nonempty S₁, S₂, S₃: S₁ ⊖ (S₂ ⊕ S₃) = (S₁ ⊖ S₂) ⊖ S₃ = (S₁ ⊖ S₃) ⊖ S₂. | n/a — restated from Danilov and Koshevoy 2000 [15, Eq. (2)]; `minkowskiDiff_add_assoc` has it for all sets | `restated` |
| `Eq. 3` | conv(S₁ ⊖ S₃, S₂ ⊖ S₃) ⊆ conv(S₁, S₂) ⊖ S₃. | n/a — restated from [16, Lemma 1]; tracked as `Lemma 1` on [Wetzlinger and Althoff 2023](../2023/wetzlinger-arxiv-backward-reachability.md) | `restated` |
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
| `Prop. 1` | (Time-point reachable set) For X₀ compact, nonempty and R̂_err centrally symmetric, R̂(Δt) = R_aff(Δt) ⊖ R̂_err + 2c ⊆ R(Δt), c = cen(R̂_err) (20). | [`MinkowskiDiffAddSubsetReachSet.lean`](../../src/CORALean/ContDynamics/NonlinearSys/Theorems/MinkowskiDiffAddSubsetReachSet.lean), [`MinkowskiDiffSubsetOfContinuousOfConvex.lean`](../../src/CORALean/ContSet/ContSet/Theorems/MinkowskiDiffSubsetOfContinuousOfConvex.lean) — `NonlinearSys.minkowskiDiff_add_subset_reachSet`: e^{AΔt} = `M` invertible, R_con = `v`, R̂_err a convex compact set as (13) makes it; the proof's representation (21) is the hypothesis `herr` (restated from [18], like (14)), the solutions and the field's Lipschitz constant along them (the paper's standing assumption) are hypotheses, and Grönwall gives the continuity of `z` the proof invokes; `minkowskiDiff_subset_of_continuous_of_convex` is `Lemma 1` with `B`, not `A`, convex | `proof-gap` — the proof applies `Lemma 1` with A = R_aff(Δt) = e^{AΔt}X₀ + R_con, which is not convex for the merely compact X₀ the proposition allows; the statement holds because R̂_err is (Findings) |
| `Prop. 2` | (Time-interval reachable set) For E = C ⊕ R̂_err centrally symmetric around c, R̂(τ₀) = conv((X₀ ⊖ C) ⊖ R̂_err, R̂(Δt) ⊖ C) + 2c ⊆ R(τ₀) (23). | — | — |
| `Def. 2` | (Support function) ρ(S, ℓ) := max_{s∈S} ℓᵀs. | n/a — restated from Le Guernic and Girard 2010 [21, Def. 1] | `restated` |
| `Def. 3` | (Polytope) P = {s \| Hs ≤ d} = ⟨H, d⟩_H. | n/a — restated from Ziegler [22, Sec. 1.1] | `restated` |
| `Eq. 24` | P ⊖ S = ⟨H, d̃⟩_H, d̃⁽ʲ⁾ = d⁽ʲ⁾ - ρ(S, H⁽ʲ,·⁾ᵀ). | n/a — restated from Kolmanovsky and Gilbert 1998 [23, Thm. 2.2] | `restated` |
| `Def. 4` | (Constrained zonotope) CZ = {c + Σ G⁽·,ⁱ⁾αᵢ \| Σ K⁽·,ⁱ⁾αᵢ = l, αᵢ ∈ [-1, 1]}; without constraints a zonotope. | n/a — restated from [24, Def. 1 and 3]; tracked as `Def. 3` on [Scott et al. 2016](../2016/scott-automatica-constrained-zonotopes.md) | `restated` |
| `Sec. IV-A` | Operation counts: linear map O(hn²), Minkowski difference O(hO(ρ)), Chebyshev center and box by linear programs, the zonotope and constrained-zonotope operations. | n/a — computational complexity, a subject CORALean does not cover | `not-covered` |
| `Alg. 1` | (Inner approximation of the reachable set) Per step: linearize at cen(R̂(t_k)) + ½Δt f(·), compute C, R_aff, R̂_aff, iterate the Lagrange remainder until L ⊆ L̂, then R̂(t_{k+1}) ← R_aff ⊖ R̂_err + 2c (Prop. 1) and R̂(τ_k) ← conv(CZ(R̂(t_k) ⊖ R̂_err ⊖ C), CZ(R̂(t_{k+1}) ⊖ C)) + 2c (Prop. 2), c = cen(C) + cen(R̂_err). | — | — |
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

**`Prop. 2` — `Lemma 1` is applied where it does not fit.** The proof writes each state as
x(t) = a + z(x(0), t) with a = x(0) + (t/Δt)(e^{AΔt}x(0) + R_con - x(0)) ∈ conv(X₀, R_aff(Δt))
and then applies `Lemma 1` with A = conv(X₀, R_aff(Δt)). The lemma needs the error as a
function φ of a; here it is a function of (x(0), t), and distinct pairs can give the same a,
so no such φ need exist. Whether (23) holds is open here; the printed proof does not show it.

**`Alg. 1`, line 15 — which centre.** `Prop. 1` shifts R_aff ⊖ R̂_err by 2 cen(R̂_err); line 15
shifts it by 2c with c = cen(C) + cen(R̂_err) from line 14, the centre `Prop. 2` uses. The two
agree only when C is centred at the origin. CORA's `linReachInner` shifts the time-point set by
nothing (its R̂_err is centred at the origin) and the time-interval sets by 2 cen(C), which is
`Prop. 1` and `Prop. 2` as printed, not line 15.
