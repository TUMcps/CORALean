# Linear Encodings for Polytope Containment Problems

S. Sadraddini and R. Tedrake. "Linear Encodings for Polytope Containment Problems". In Proc. of the 58th IEEE Conference on Decision and Control (CDC), pp. 4367-4372, 2019. arXiv:1903.05214.

**Source:** https://arxiv.org/pdf/1903.05214 (arXiv v1, 12 Mar 2019, 17 pages, read in full; text extracted with `pypdf`). The arXiv version is the long one ("Shorter version submitted to CDC 2019"); the IEEE version was not reachable (the MIT repository copy sits behind a captcha). Numbering is the arXiv version's, which is what most of CORA cites (`Theorem 3`, `Proposition 6`, `Corollary 6`, `Eq. (42)`, `(43)`); the shorter CDC version numbers differently — CORA's `priv_zonotopeContainment_SadraddiniTedrake.m` and the ECC 2024 paper cite the zonotope condition, `Thm. 3` here, as its "Corollary 4".  
**Inventory:** confirmed (against arXiv v1: Definitions 1-5, Lemmas 1-2, Theorems 1-3, Propositions 1-7, Corollaries 1-6, Remarks 1-3 and Examples 1-7, each with its own counter; the equations below are the numbered displays that make a claim)

Sufficient linear-programming conditions for one polytope to contain another when both are
affine images of H-polytopes ("AH-polytopes"), so that a zonotope, a Minkowski sum or a
convex hull never has to be put into halfspaces. CORA's `zonotope/contains_` method
`'approx:st'` is `Thm. 3`, its `conZonotope/contains_` uses `Thm. 1`, and `reduce` /
`reduceUnderApprox` with `'sadraddini'` are `Prop. 6` and `Cor. 6`. The weak-duality half of
every encoding is `HPolytope.mem_ineqs_of_cert`; the "only if" halves rest on Farkas' lemma,
proved for this page (`Global/LinProg/Farkas.lean`). Several equivalences omit a
nonemptiness hypothesis and are false at an empty polytope; one sign in `Prop. 7` is wrong.

## Results

| Result | What it says | In CORALean | Class |
|---|---|---|---|
| `Def. 1` | (H-Polytope) P = {x \| Hx ≤ h} with ker(H) = {0}. | n/a — the textbook halfspace representation, restated from Ziegler | `restated` |
| `Def. 2` | (AH-polytope) X = x̄ + X P, an affine image of an H-polytope P ⊂ ℝ^m. | [`AHPolytope.lean`](../../src/CORALean/ContSet/HPolytope/Real/Definitions/AHPolytope.lean) — a set, `HPolytope.ahPolytope`; `ConZonotope` is the representation of the same sets | `correct` |
| `Eq. 4` | If X has a left inverse X† (X†X = I), then {x̄ + Xx \| Hx ≤ h} = {y \| HX†y ≤ h + HX†x̄}. | [`AHPolytopeEqOfLeftInverseCounterexample.lean`](../../src/CORALean/ContSet/HPolytope/Real/Theorems/AHPolytopeEqOfLeftInverseCounterexample.lean), [`AHPolytopeEqOfLeftInverse.lean`](../../src/CORALean/ContSet/HPolytope/Real/Theorems/AHPolytopeEqOfLeftInverse.lean) — the counterexample, and the identity with the equality row `(I - XX†)(y - x̄) = 0` added **Counterexample:** `HPolytope.ahPolytope_eq_of_leftInverse_counterexample` | `fixed` — false for a non-square X (the right side is a cylinder along ker X†; (0, 1) for X = (1, 0)ᵀ); exact with the equality row; see Findings |
| `Eq. 5` | (Affine transformation) G(x̄ + XP) + g = (Gx̄ + g) + GXP. | [`AHPolytopeImageAffine.lean`](../../src/CORALean/ContSet/HPolytope/Real/Theorems/AHPolytopeImageAffine.lean) | `correct` |
| `Eq. 6` | (Minkowski sum) (x̄₁ + X₁P₁) ⊕ (x̄₂ + X₂P₂) = x̄₁ + x̄₂ + (X₁, X₂)P_⊕, P_⊕ = {z \| blk(H₁, H₂)z ≤ [h₁, h₂]}. | [`AHPolytopeAddEq.lean`](../../src/CORALean/ContSet/HPolytope/Real/Theorems/AHPolytopeAddEq.lean) — `(X₁, X₂)` and `blk` written out over `Fin (n₁ + n₂)` | `correct` |
| `Eq. 7` | (Intersection) Eliminating p₂ = X₂†(X₁p₁ + x̄₁ - x̄₂) + (I - X₂†X₂)w: (x̄₁ + X₁P₁) ∩ (x̄₂ + X₂P₂) = (X₁, 0)P_∩, P_∩ = {z \| [(H₁, 0), (H₂X₂†X₁, I - X₂†X₂)]z ≤ [h₁, h₂ + X₂†(x̄₂ - x̄₁)]}. | [`AHPolytopeInterEqCounterexample.lean`](../../src/CORALean/ContSet/HPolytope/Real/Theorems/AHPolytopeInterEqCounterexample.lean), [`AHPolytopeInterEq.lean`](../../src/CORALean/ContSet/HPolytope/Real/Theorems/AHPolytopeInterEq.lean) — the counterexample to the formula read so that it type-checks, and the corrected identity at any generalized inverse `X₂X₂†X₂ = X₂` **Counterexample:** `HPolytope.ahPolytope_inter_eq_counterexample` | `fixed` — ill-typed as printed (H₂ missing on the w block), the offset x̄₁ is dropped, and without the range row (I - X₂X₂†)(X₁p₁ + x̄₁ - x̄₂) = 0 it is false (X₂ = 0); exact with all three; see Findings |
| `Def. 3` | (Unit Box) Bⁿ = {x \| ‖x‖∞ ≤ 1} = {x \| [I, -I]x ≤ 1}. | n/a — the supremum-norm unit ball, `HPolytope.unitBox` | `restated` |
| `Def. 4` | (Full-Dimensional Polytope) ∃ x̄ ∈ P, ε > 0 with x̄ + εBⁿ ⊂ P. | n/a — nonempty interior, `ContSet.IsFullDim` | `restated` |
| `Def. 5` | (Zonotope) ⟨x̄, X⟩ = x̄ + XB^{nx}, order nx/n. | n/a — restated; tracked as `Def. 1` on [Girard 2005](../2005/girard-hscc-reachability-zonotopes.md) | `restated` |
| `Lemma 1` | (H-Polytope in H-Polytope) {Hₓx ≤ hₓ} ⊆ {H_y y ≤ h_y} iff ∃Λ ≥ 0 with ΛHₓ = H_y and Λhₓ ≤ h_y (Eq. 8). | [`IneqsSubsetIff.lean`](../../src/CORALean/ContSet/HPolytope/Real/Theorems/IneqsSubsetIff.lean), [`IneqsSubsetIffCounterexample.lean`](../../src/CORALean/ContSet/HPolytope/Real/Theorems/IneqsSubsetIffCounterexample.lean) — the iff for a nonempty inbody, by Farkas' lemma row by row, and the counterexample at an empty one | `underspecified` — fails only at an empty inbody ({x₁ ≤ -1, -x₁ ≤ -1, x₂ ≤ 0} = ∅ lies in the unit box, and no Λ ≥ 0 assembles the row (0, -1)), which the paper's setting excludes; `X ≠ ∅` is supplied; see Findings |
| `Thm. 1` | (Sufficient Conditions for AH-polytope in AH-polytope) For full-dimensional Pₓ, x̄ + XPₓ ⊆ ȳ + YP_y if ∃Γ, β, Λ ≥ 0 with X = YΓ, ȳ - x̄ = Yβ, ΛHₓ = H_yΓ, Λhₓ ≤ h_y + H_yβ (Eq. 12); geometrically -β + ΓPₓ ⊆ P_y (Eq. 17). | [`AHPolytopeSubsetOfExistsCert.lean`](../../src/CORALean/ContSet/HPolytope/Real/Theorems/AHPolytopeSubsetOfExistsCert.lean) — the printed statement: for a full-dimensional `Pₓ`, a certificate `Γ, β, Λ ≥ 0` of (12) gives the containment; [`AHPolytopeSubsetOfCert.lean`](../../src/CORALean/ContSet/HPolytope/Real/Theorems/AHPolytopeSubsetOfCert.lean), [`MemIneqsOfCert.lean`](../../src/CORALean/ContSet/HPolytope/Real/Theorems/MemIneqsOfCert.lean) — the same from a given certificate with no full-dimensionality, which the converse alone uses, and (17) on the way | `correct` |
| `Thm. 2` | The conditions (12) are necessary if range(H'_y† Y') ⊕ ker(H'_y) = ℝ^{qy} (Eq. 18). | [`AHPolytopeCertNecessary.lean`](../../src/CORALean/ContSet/HPolytope/Real/Theorems/AHPolytopeCertNecessary.lean) — `H'_y†` read through `H'_y H'_y† = I`, which the Moore-Penrose inverse has under `Def. 1`'s ker H_y = {0}; Pₓ full-dimensional as in `Thm. 1`. The hypothesis forces Y injective, so this is `Cor. 1` | `correct` |
| `Cor. 1` | The conditions (12) are necessary and sufficient if Y has a left inverse (linearly independent columns). | [`AHPolytopeSubsetIffOfInjective.lean`](../../src/CORALean/ContSet/HPolytope/Real/Theorems/AHPolytopeSubsetIffOfInjective.lean) — Y injective, Pₓ full-dimensional (`Thm. 1`'s hypothesis), which puts the columns of X and ȳ - x̄ in range Y | `correct` |
| `Cor. 2` | (AH-polytope in H-polytope) The containment is `Cor. 1` at Y = I: the linear program (12), which is lossless. | [`AHPolytopeSubsetIneqsIff.lean`](../../src/CORALean/ContSet/HPolytope/Real/Theorems/AHPolytopeSubsetIneqsIff.lean) — `HPolytope.ahPolytope_subset_ineqs_iff`: x̄ + XPₓ ⊆ P_y iff (12) holds at Y = I, ȳ = 0, for any nonempty Pₓ (weaker than `Thm. 1`'s full-dimensionality, which the proof does not use) | `correct` |
| `Cor. 2 (complexity)` | The AH-polytope in H-polytope containment problem can be decided in polynomial time. | n/a — restated: the paper calls it "a known result in the literature", a version of which is derived in Kellner, *Containment problems for projections of polyhedra and spectrahedra* (arXiv:1509.02735), which has no page here; the time is that of the linear program of `Cor. 2` | `restated` |
| `Remark 1` | X and x̄ appear linearly in (12), so they may be decision variables of a larger convex program. | n/a — an observation about the encoding, not a claim to formalize | `not-a-claim` |
| `Thm. 3` | (Zonotope in Zonotope Containment) ⟨x̄, X⟩ ⊆ ⟨ȳ, Y⟩ if ∃Γ, β with X = YΓ, ȳ - x̄ = Yβ, ‖(Γ, β)‖∞ ≤ 1 (Eq. 19). | [`SubsetOfCert.lean`](../../src/CORALean/ContSet/Zonotope/Real/Theorems/SubsetOfCert.lean), [`ContainsST.lean`](../../src/CORALean/ContSet/Zonotope/Real/Operations/ContainsST.lean), [`ContainsSTSound.lean`](../../src/CORALean/ContSet/Zonotope/Real/Theorems/ContainsSTSound.lean) — in generators, over any real module; `containsST` is CORA's `'approx:st'`, checking a solver's `(Γ, β)` | `correct` |
| `Example 1` | A pair of zonotopes in ℝ² whose containment `Thm. 3` verifies, lost when the last column of Y is dropped (Fig. 1). | n/a — an illustration | `not-a-claim` |
| `Example 2` | A pair in ℝ³ with Zₓ ⊆ Z_y that `Thm. 3` cannot verify (feasible only after scaling Zₓ by 0.9915). | n/a — an illustration of the loss, found by search | `not-a-claim` |
| `Sec. IV-A` | Conservativeness of `Thm. 3` on 10000 random zonotope pairs: loss below 0.01 for 98% (Fig. 2). | n/a — an experiment | `not-a-claim` |
| `Remark 2` | For zonotopes given as {x \| ‖H(x - x̄)‖∞ ≤ 1} the H-form is available, so `Lemma 1` is exact there and the LMI condition of Han et al. is not needed. | n/a — a comparison with another paper's method | `not-a-claim` |
| `Prop. 1` | (Minkowski sum as the inbody) x̄ + ⨁ᵢ XᵢP_{x,i} ⊆ P_y iff ∃Λᵢ ≥ 0 with ΛᵢH_{x,i} = H_yXᵢ, Σᵢ Λᵢh_{x,i} ≤ h_y - H_yx̄ (Eq. 23). | [`SumAHPolytopeSubsetIneqsIff.lean`](../../src/CORALean/ContSet/HPolytope/Real/Theorems/SumAHPolytopeSubsetIneqsIff.lean), [`SumAHPolytopeSubsetIneqsIffCounterexample.lean`](../../src/CORALean/ContSet/HPolytope/Real/Theorems/SumAHPolytopeSubsetIneqsIffCounterexample.lean) — the iff for nonempty summands (one Farkas per row of H_y, over the product of the coefficient spaces), and `Lemma 1`'s counterexample at N = 1 | `underspecified` — at N = 1 this is `Lemma 1`, failing only at an empty summand, which the paper's setting excludes; every P_{x,i} nonempty is supplied; see Findings |
| `Prop. 2` | (Minkowski Sum as the Circumbody) x̄ + XPₓ ⊆ ⨁ᵢ(ȳᵢ + YᵢP_{y,i}) if ΛᵢHₓ = H_{y,i}Γᵢ, Λᵢhₓ ≤ h_{y,i} + H_{y,i}βᵢ, Σᵢ(ȳᵢ - Yᵢβᵢ) = x̄, ΣᵢYᵢΓᵢ = X (Eq. 24). | [`AHPolytopeSubsetSumOfCert.lean`](../../src/CORALean/ContSet/HPolytope/Real/Theorems/AHPolytopeSubsetSumOfCert.lean) | `correct` |
| `Example 3` | A triangle and a thin box in ℝ²: `Prop. 2` fails to verify P_sum ⊆ P₁ ⊕ P₂ but verifies λP_sum for λ ≤ 0.68 (Fig. 3). | n/a — an illustration of the loss | `not-a-claim` |
| `Prop. 3` | (Convex Hull of H-polytopes as the Circumbody) x̄ + XPₓ ⊆ Convexhull({P_{y,i}}) if ∃Λᵢ ≥ 0, λᵢ ≥ 0, βᵢ, Γᵢ with ΛᵢHₓ = H_{y,i}Γᵢ, Λᵢhₓ ≤ λᵢh_{y,i} + H_{y,i}βᵢ, Σλᵢ = 1, Σ-βᵢ = x̄, ΣΓᵢ = X (Eq. 25). | [`AHPolytopeSubsetConvexHullOfCert.lean`](../../src/CORALean/ContSet/HPolytope/Real/Theorems/AHPolytopeSubsetConvexHullOfCert.lean), [`AHPolytopeSubsetConvexHullOfCertCounterexample.lean`](../../src/CORALean/ContSet/HPolytope/Real/Theorems/AHPolytopeSubsetConvexHullOfCertCounterexample.lean) — for nonempty bounded P_{y,i}, and the counterexample at an empty one | `underspecified` — fails only at an empty P_{y,i}, where {H y ≤ 0·h} is a cone rather than 0·P (P₁ = {0}, P₂ = ∅ in ℝ²), which the paper's setting excludes; nonempty bounded P_{y,i} is supplied; see Findings |
| `Lemma 2` | (Σᵢ Aᵢ)S ⊆ ⨁ᵢ AᵢS for any set S. | [`SumMulVecImageSubset.lean`](../../src/CORALean/Global/SumMulVecImageSubset.lean) | `correct` |
| `Cor. 3` | (Convex Hull of AH-Polytopes as the Circumbody) x̄ + XPₓ ⊆ Convexhull({ȳᵢ + YᵢP_{y,i}}) if ΛᵢHₓ = H_{y,i}Γᵢ, Λᵢhₓ ≤ λᵢh_{y,i} + H_{y,i}βᵢ, λᵢ ≥ 0, (1, x̄, X) = Σᵢ(λᵢ, λᵢȳᵢ - Yᵢβᵢ, YᵢΓᵢ) (Eq. 28). | [`AHPolytopeSubsetConvexHullAHOfCert.lean`](../../src/CORALean/ContSet/HPolytope/Real/Theorems/AHPolytopeSubsetConvexHullAHOfCert.lean), [`AHPolytopeSubsetConvexHullAHOfCertCounterexample.lean`](../../src/CORALean/ContSet/HPolytope/Real/Theorems/AHPolytopeSubsetConvexHullAHOfCertCounterexample.lean) — for nonempty bounded P_{y,i}, and `Prop. 3`'s counterexample at Yᵢ = I, ȳᵢ = 0 | `underspecified` — `Prop. 3`'s gap: fails only at an empty P_{y,i}, which the paper's setting excludes; nonempty bounded ones are supplied; see Findings |
| `Prop. 4` | (Disjunctive Containment Problem) ⋁ᵢ(x̄ + XPₓ ⊆ P_{y,i}) iff ∃Λᵢ ≥ 0, δᵢ ∈ {0, 1}, βᵢ, Γᵢ with ΛᵢHₓ = H_{y,i}Γᵢ, Λᵢhₓ ≤ δᵢh_{y,i} - H_{y,i}βᵢ, Σδᵢ = 1, Σβᵢ = x̄, ΣΓᵢ = X (Eq. 31). | [`ExistsSubsetIffDisjunctiveCert.lean`](../../src/CORALean/ContSet/HPolytope/Real/Theorems/ExistsSubsetIffDisjunctiveCert.lean), [`ExistsSubsetIffDisjunctiveCertCounterexample.lean`](../../src/CORALean/ContSet/HPolytope/Real/Theorems/ExistsSubsetIffDisjunctiveCertCounterexample.lean) — the iff for Pₓ nonempty and every P_{y,i} nonempty and bounded; the counterexample to "if" at an empty P_{y,i} (and `Lemma 1`'s to "only if" at an empty Pₓ, N = 1) | `underspecified` — "if" fails only at an empty P_{y,i} (`Prop. 3`'s data with δ = (1, 0)) and "only if" only at an empty Pₓ, which the paper's setting excludes; both nonempty and P_{y,i} bounded are supplied; see Findings |
| `Cor. 4` | (Zonotope in the Convexhull of Zonotopes) ⟨x̄, X⟩ ⊆ Convexhull(⋃ᵢ⟨ȳᵢ, Yᵢ⟩) if ‖(Γᵢ \| βᵢ)‖∞ ≤ λᵢ, Σλᵢ = 1, ΣᵢYᵢβᵢ + λᵢȳᵢ = x̄, ΣᵢYᵢΓᵢ = X (Eq. 33). | [`SubsetConvexHullOfCert.lean`](../../src/CORALean/ContSet/Zonotope/Real/Theorems/SubsetConvexHullOfCert.lean) — in generators, over any real module; zonotopes are nonempty and bounded, so `Cor. 3`'s gap does not arise | `correct` |
| `Cor. 5` | (Disjunctive Containment of Zonotopes) ⋁ᵢ(⟨x̄, X⟩ ⊆ ⟨ȳᵢ, Yᵢ⟩) if ‖(Γᵢ \| βᵢ)‖∞ ≤ δᵢ ∈ {0, 1}, Σδᵢ = 1, ΣᵢYᵢβᵢ + δᵢȳᵢ = x̄, ΣᵢYᵢΓᵢ = X (Eq. 35). | [`ExistsSubsetOfDisjunctiveCert.lean`](../../src/CORALean/ContSet/Zonotope/Real/Theorems/ExistsSubsetOfDisjunctiveCert.lean) | `correct` |
| `Prop. 5` | The linear program (39) gives an upper bound D on the Hausdorff distance of two AH-polytopes (in the norm of P_Ball = {H_Ball x ≤ h_Ball}). | [`AHPolytopeSubsetAddBallOfCert.lean`](../../src/CORALean/ContSet/HPolytope/Real/Theorems/AHPolytopeSubsetAddBallOfCert.lean), [`HausdorffDistLeOfSubsetAddBall.lean`](../../src/CORALean/ContSet/HPolytope/Real/Theorems/HausdorffDistLeOfSubsetAddBall.lean) — a feasible point gives X₁ ⊆ X₂ ⊕ D P_Ball and back (Eq. 40), for any P_Ball; read as Mathlib's `hausdorffDist` when P_Ball is the supremum-norm ball, the paper's norm | `underspecified` — two indices of (39) are misprinted (`Λ₃H₄ = H_BallΓ₄` for `Λ₄H₂`, `Λ₃h₂ ≤ h₂ + H₁β₃` for `h₁`); read as `Prop. 2` gives them |
| `Example 4` | Hausdorff bounds D₁₂ ≤ 2, D₂₁ ≤ 3 for `Example 1`'s zonotopes (Fig. 4). | n/a — an illustration | `not-a-claim` |
| `Remark 3` | d_H(C₁, C₂) = max_{c ∈ P_Ball} \|max_{C₁} c'x - max_{C₂} c'x\| for compact convex sets (Eq. 41); sampling c gives a lower bound. | n/a — the support-function form of the Hausdorff distance, recalled from the literature to compare methods | `restated` |
| `Prop. 6` | (Optimal Zonotope Order Reduction - Outer Approximation) With X = X_red Γ₀, X_red = XΓ₁ + Δ, ‖[Γ₀, Γ₁]‖∞ ≤ 1, ‖Δ‖∞ ≤ δ (Eq. 42): Z ⊆ Z_red and d_H(Z, Z_red) ≤ δ*. | [`HausdorffDistLeOfReduceCert.lean`](../../src/CORALean/ContSet/Zonotope/Real/Theorems/HausdorffDistLeOfReduceCert.lean) — at every feasible point, so at the optimum; supremum-norm Hausdorff distance | `correct` |
| `Cor. 6` | (Optimal Zonotope Order Reduction - Inner Approximation) With X_red = XΓ₀, X = X_red Γ₁ + Δ, ‖[Γ₀, Γ₁]‖∞ ≤ 1, ‖Δ‖∞ ≤ δ (Eq. 43): Z_red ⊆ Z and d_H(Z, Z_red) ≤ δ*. | [`HausdorffDistLeOfReduceInnerCert.lean`](../../src/CORALean/ContSet/Zonotope/Real/Theorems/HausdorffDistLeOfReduceInnerCert.lean), [`ReduceUnderApproxSadraddini.lean`](../../src/CORALean/ContSet/Zonotope/Real/Operations/ReduceUnderApproxSadraddini.lean), [`ReduceUnderApproxSadraddiniInner.lean`](../../src/CORALean/ContSet/Zonotope/Real/Theorems/ReduceUnderApproxSadraddiniInner.lean) — `Prop. 6` with the roles exchanged; the statement's "G" is X. CORA's `reduceUnderApprox(Z, 'sadraddini')` checks a solver's candidate against (43)'s containment rows | `correct` |
| `Example 5` | Iterative outer and inner order reduction of a 2-D zonotope of order 6 to order 2 (Fig. 5). | n/a — an illustration of the bilinear iteration | `not-a-claim` |
| `Prop. 7` | For F = {(x, u) \| Hx + Fu ≤ g} and its projection F_proj, a feasible H_x of (45) with cost ε gives X = x̄ + {H_x x ≤ 1} ⊆ F_proj and d_H(X, F_proj) ≤ ε. | [`ProjectionInnerOfCertCounterexample.lean`](../../src/CORALean/ContSet/HPolytope/Real/Theorems/ProjectionInnerOfCertCounterexample.lean), [`ProjectionInnerOfCert.lean`](../../src/CORALean/ContSet/HPolytope/Real/Theorems/ProjectionInnerOfCert.lean) — the counterexample to the printed program, and the corrected one: X ⊆ F_proj and F_proj ⊆ X ⊕ εP_Ball **Counterexample:** `HPolytope.projection_inner_of_cert_counterexample` | `fixed` — the row Λ₂g ≤ εh_Ball - H_Ball x̄ + H_Ball βₓ has the wrong sign on x̄ (it certifies F_proj ⊆ -x̄ + X₀ ⊕ εP_Ball): in ℝ¹, F = [-4, 2], X = [0, 2], ε = 2 is feasible while d_H = 4; true with + H_Ball x̄; see Findings |
| `Example 6` | Inner approximation of a 20-step MPC feasible set (a projection from ℝ²² to ℝ²) by 4 and 6 hyperplanes (Fig. 6). | n/a — an experiment | `not-a-claim` |
| `Example 7` | Polytopic-tree control of an inverted pendulum with a wall, zonotope containment by `Thm. 3` (Figs. 7-8). | n/a — an experiment | `not-a-claim` |
| `Table I` | The encodings of `Lemma 1` to `Cor. 5`, side by side, with which are lossless. | n/a — a summary of results with their own rows | `not-a-claim` |

## Findings

**`Lemma 1`, and with it `Prop. 1`, `Prop. 4` — an empty inbody.** `Lemma 1` is printed as an
iff for any H-polytopes. Its "only if" is Farkas' lemma, which needs the inbody nonempty: in
ℝ², X = {x₁ ≤ -1, -x₁ ≤ -1, x₂ ≤ 0} is empty (ker Hₓ = {0}, as `Def. 1` asks), so X ⊆ Y for
Y the unit box, yet the box's row (0, -1) is no nonnegative combination of (1, 0), (-1, 0),
(0, 1). `Prop. 1` at N = 1, x̄ = 0, X₁ = I is the same statement, and so is the "only if"
of `Prop. 4` at N = 1. All three hold once the inbody (every summand) is nonempty.
[`IneqsSubsetIffCounterexample.lean`](../../src/CORALean/ContSet/HPolytope/Real/Theorems/IneqsSubsetIffCounterexample.lean),
[`SumAHPolytopeSubsetIneqsIffCounterexample.lean`](../../src/CORALean/ContSet/HPolytope/Real/Theorems/SumAHPolytopeSubsetIneqsIffCounterexample.lean)

**`Prop. 3`, `Cor. 3`, `Prop. 4` — a zero weight on an empty circumbody.** The proofs read
`{H_{y,i} y ≤ λᵢ h_{y,i}}` as λᵢP_{y,i} (Eq. 26), and at λᵢ = 0 (or δᵢ = 0) conclude the
summand vanishes. {H y ≤ 0} is the recession cone, which is {0} exactly when P is nonempty
and bounded; an empty P can leave any cone. In ℝ², with P₁ = {0},
P₂ = {x₁ ≤ -1, -x₁ ≤ -1, x₂ ≤ 0} = ∅ (bounded, ker H₂ = {0}), Pₓ = {0} × [-1, 0], x̄ = 0,
X = I, the weights λ = (1, 0), β = 0, Γ = (0, I) satisfy (25) — the second summand only has
to meet x₁ = 0, x₂ ≤ 0 — but conv(P₁ ∪ P₂) = {0} misses (0, -1). The same data with
Yᵢ = I, ȳᵢ = 0 breaks `Cor. 3`, and with δ = (1, 0) the "if" of `Prop. 4`. All three hold
for nonempty bounded P_{y,i}, which zonotopes always are (`Cor. 4`, `Cor. 5`).
[`AHPolytopeSubsetConvexHullOfCertCounterexample.lean`](../../src/CORALean/ContSet/HPolytope/Real/Theorems/AHPolytopeSubsetConvexHullOfCertCounterexample.lean),
[`AHPolytopeSubsetConvexHullAHOfCertCounterexample.lean`](../../src/CORALean/ContSet/HPolytope/Real/Theorems/AHPolytopeSubsetConvexHullAHOfCertCounterexample.lean),
[`ExistsSubsetIffDisjunctiveCertCounterexample.lean`](../../src/CORALean/ContSet/HPolytope/Real/Theorems/ExistsSubsetIffDisjunctiveCertCounterexample.lean)

**`Eq. 4` — a left inverse is not an inverse.** `{y | HX†y ≤ h + HX†x̄}` constrains only the
component of y - x̄ that X† sees: for X = (1, 0)ᵀ, X† = (1, 0), H = (1, -1)ᵀ, h = 1 it is the
strip |y₁| ≤ 1, containing (0, 1), while the AH-polytope is a segment of the first axis. The
missing rows are (I - XX†)(y - x̄) = 0; with them the identity holds for any left inverse.
[`AHPolytopeEqOfLeftInverseCounterexample.lean`](../../src/CORALean/ContSet/HPolytope/Real/Theorems/AHPolytopeEqOfLeftInverseCounterexample.lean)

**`Eq. 7` — the intersection.** As printed P_∩'s second block row `(H₂X₂†X₁, I - X₂†X₂)`
does not type-check (H₂ is missing on the w block), the result `(X₁, 0)P_∩` drops x̄₁, and —
the substantive error — the parametrization p₂ = X₂†v + (I - X₂†X₂)w covers the solutions of
X₂p₂ = v only when one exists. Read with H₂ and x̄₁ restored, X₁ = [-1, 1] and X₂ = {5}
(X₂ = 0, X₂† = 0) have empty intersection, while the formula returns [-1, 1]. Adding the
row (I - X₂X₂†)(X₁p₁ + x̄₁ - x̄₂) = 0 makes it exact for any X₂† with X₂X₂†X₂ = X₂.
[`AHPolytopeInterEqCounterexample.lean`](../../src/CORALean/ContSet/HPolytope/Real/Theorems/AHPolytopeInterEqCounterexample.lean)

**`Prop. 5` — two indices.** (39) has `Λ₃H₄ = H_BallΓ₄` (no H₄ exists; `Λ₄H₂`) and
`Λ₃h₂ ≤ h₂ + H₁β₃` (`h₁`, as `Prop. 2` gives for X₂ ⊆ X₁ ⊕ DP_Ball). With those read, the
bound holds for any polytopic ball.

**`Prop. 7` — the sign of x̄.** The second containment (I, 0)F ⊆ x̄ + X₀ ⊕ εB, by `Thm. 1`
with circumbody offset x̄, needs Λ₂g ≤ εh_Ball + H_Ball x̄ + H_Ball βₓ; (45) prints
`- H_Ball x̄`, which certifies the containment in -x̄ + X₀ ⊕ εB instead. In ℝ¹ with no u,
F = {x ≤ 2, -x ≤ 4}, x̄ = 1, H_x = (1, -1)ᵀ (X = [0, 2]), P_Ball = [-1, 1], ε = 2, the weights
Λ₀ = I, Λ₁ = I/3, Λ₂ = 2I/3, X₁ = 1/3, βₓ = 1/3 meet every printed row, but
d_H(X, F_proj) = 4. Two further misprints are read the only way the dimensions allow
(`H_B` is `H_Ball`; `h_Ball` in `Λ₁g ≤ h_Ball - H_xβₓ` is `1`). The paper's own example
takes x̄ = 0, where the sign does not matter.
[`ProjectionInnerOfCertCounterexample.lean`](../../src/CORALean/ContSet/HPolytope/Real/Theorems/ProjectionInnerOfCertCounterexample.lean)
