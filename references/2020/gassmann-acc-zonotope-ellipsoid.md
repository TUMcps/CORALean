# Scalable Zonotope-Ellipsoid Conversions using the Euclidean Zonotope Norm

V. Gaßmann and M. Althoff. "Scalable Zonotope-Ellipsoid Conversions using the Euclidean Zonotope Norm". In Proc. of the 2020 American Control Conference (ACC), pp. 4715-4721, 2020.

**Source:** https://mediatum.ub.tum.de/doc/1554653/document.pdf (the TUM repository copy, 7 pages, read in full; text extracted with `pypdf`; it carries the DOI 10.23919/ACC45564.2020.9147938 of the ACC version, whose pages 4715-4721 are from the DOI record. IEEE Xplore was not reachable.)  
**Inventory:** confirmed (the numbered items are Definitions 1-4, Lemmas 1-5, Proposition 1, Theorems 1-4, Example 1, equations (1)-(30), Tables I-II and Figures 1-2; each definition, lemma and theorem is a row with its own displays, the other displays that make a claim are rows of their own, and the remarks and paragraphs that make one are rows named by section)

The paper behind CORA's norm-based conversions between zonotopes and ellipsoids
(`zonotope/ellipsoid` with `'outer:norm'`, `'outer:norm_bnd'` and `'inner:norm'`, and
`ellipsoid/zonotope` with `'outer:norm'` and `'inner:norm'`). Each conversion transforms the
ellipsoid into a sphere and scales by a bound on the zonotope's maximum or minimum Euclidean
norm: the maximum as a sign-vector program (`Prop. 1`) or its semidefinite dual (`Lemma 3`), the
minimum from the halfspace representation (`Def. 4`) or a test on the axes (`Lemma 5`). The tree's
ellipsoids store a generator rather than a shape matrix, so the transformation `E₀^{-1/2}` is any
invertible factor of `E₀`, which changes no norm. `Lemma 5` checks the wrong points when the
zonotope is not centred at the origin; `Def. 4` needs normalized rows. The volume optimality of
the parallelotope case and the duality-gap discussion are not yet formalized.

## Results

| Result | What it says | In CORALean | Class |
|---|---|---|---|
| `Def. 1` | (Zonotope) `Z(G, z̄) = {G x + z̄ \| \|x\| ≤ 1}`, full-dimensional: `G ∈ ℝ^{n×m}`, `n ≤ m`, `rank G = n` (Eq. 1); also its vertex and halfspace representations. | n/a — restated; tracked as `Def. 1` on [Girard 2005](../2005/girard-hscc-reachability-zonotopes.md) | `restated` |
| `Def. 2` | (Ellipsoid) `E(E, ē) = {x \| (x - ē)ᵀ E⁻¹ (x - ē) ≤ 1}`, `E ≻ 0` (Eq. 2). | n/a — the textbook shape-matrix form; the tree's `Ellipsoid` stores a generator `G` with shape `G Gᵀ` (`Ellipsoid.shape`) | `restated` |
| `Lemma 1` | (Linear transformation of a zonotope) `T Z(G, z̄) = Z(T G, T z̄)` (Eq. 3). | n/a — restated; tracked as `Sec. 2` on [Girard 2005](../2005/girard-hscc-reachability-zonotopes.md) | `restated` |
| `Lemma 2` | (Linear transformation of an ellipsoid) For non-singular `T`, `T E(E, ē) = E(T E Tᵀ, T ē)` (Eq. 4). | [`MtimesExact.lean`](../../src/CORALean/ContSet/Ellipsoid/Real/Theorems/MtimesExact.lean), [`ShapeMtimes.lean`](../../src/CORALean/ContSet/Ellipsoid/Real/Theorems/ShapeMtimes.lean) — exact for every `T` in the generator form, and the shape `T E Tᵀ` | `correct` |
| `Def. 3` | (Squared maximum zonotope norm) `⌈Z(G, z̄)⌉² = max_{\|u\| ≤ 1} uᵀ Gᵀ G u` (Eq. 5). | [`MaxNormSq.lean`](../../src/CORALean/ContSet/Zonotope/Real/Definitions/MaxNormSq.lean), [`SqNormLeMaxNormSq.lean`](../../src/CORALean/ContSet/Zonotope/Real/Theorems/SqNormLeMaxNormSq.lean), [`SqNormSumEqGram.lean`](../../src/CORALean/ContSet/Zonotope/Real/Theorems/SqNormSumEqGram.lean) | `correct` |
| `Def. 4` | (Squared minimum zonotope norm) `⌊Z(G, z̄)⌋² = min(b²)` for `{z \| A z ≤ b}` the halfspace representation of `Z(G, 0)` (Eq. 6). | [`IsGreatestBallRadius.lean`](../../src/CORALean/ContSet/HPolytope/Real/Theorems/IsGreatestBallRadius.lean) — with unit rows the largest centred ball has radius `min b` and `(min b)² = min(b²)` | `underspecified` — `min(b²)` is the squared inradius only for normalized rows, which the derivation assumes and the definition omits; see Findings |
| `Eq. 10` | (Eqs. 7-10) The radius `s*` of the largest ball in `Z(G, 0)` satisfies `s*² = min(b²)` when the rows `aᵢ` are normed: the ball of radius `s` lies in `aᵢᵀ z ≤ bᵢ` iff `s ≤ bᵢ`. | [`IsGreatestBallRadius.lean`](../../src/CORALean/ContSet/HPolytope/Real/Theorems/IsGreatestBallRadius.lean) | `correct` |
| `Sec. III-A (Remark a)` | For `n = m`, `Z(I, ẑ) = G⁻¹ Z(G, z̄)` (Eq. 12); the minimum-volume ellipsoid covering a hypercube is the sphere of radius `√n` [14, 4.1], so that of `Z(G, z̄)` is `E(n G Gᵀ, z̄)`. | — | — |
| `Eq. 11` | The minimum-volume enclosing ellipsoid of a zonotope from its vertices, `min -log det E` s.t. `(vᵢ - c)ᵀ E⁻¹ (vᵢ - c) ≤ 1` [9, Sec. 8.4.1]. | n/a — restated from Boyd and Vandenberghe's *Convex Optimization*, which has no page here | `restated` |
| `Sec. III-A (Remark b)` | The variation of Goffin's algorithm [14] gives an enclosing ellipsoid that is not tight (Fig. 1). | n/a — an illustration | `not-a-claim` |
| `Eq. 13` | The initial guess `E(E₀, z̄) = E(m G Gᵀ, z̄)` of [14, Sec. 4.1]. | n/a — restated from Černý's *Goffin's algorithm for zonotopes*, which has no page here; it is the `E₀` of `Thm. 1` | `restated` |
| `Sec. III-B (initial guess)` | With `L = G [B -B]`, `[B -B]` all `2ᵐ` sign vectors and the rows of `B` orthogonal, the samples have mean `0` and covariance `c G Gᵀ`, `c > 0`: the initial guess is aligned with their principal axes. | [`SignSumCovariance.lean`](../../src/CORALean/ContSet/Zonotope/Real/Theorems/SignSumCovariance.lean) — mean `0` and `∑ (G u)(G u)ᵀ = 2ᵐ G Gᵀ` over all sign vectors | `correct` |
| `Eq. 14` | By Def. 3, `⌈Z⌉² = max_{u ∈ {-1, 1}ᵐ} uᵀ Gᵀ G u`. | [`MaxNormSqEqSign.lean`](../../src/CORALean/ContSet/Zonotope/Real/Theorems/MaxNormSqEqSign.lean) — the box maximum is taken at a sign vector, by convexity on the vertex hull | `correct` |
| `Prop. 1` | `⌈Z(G, z̄)⌉² = -min_{u ∈ {-1, 1}ᵐ} uᵀ M u + λ_max m` with `M = -(GᵀG - λ_max I) ≽ 0`, `λ_max` the largest eigenvalue of `GᵀG` (Eq. 15). | [`MaxNormSqEqSign.lean`](../../src/CORALean/ContSet/Zonotope/Real/Theorems/MaxNormSqEqSign.lean) — the identity for every `λ`; `M ≽ 0` for every `λ` bounding the Rayleigh quotient of `GᵀG`, of which `λ_max` is the least | `correct` |
| `Eq. 16` | For non-singular `T`, `Z ⊆ E ⇔ T Z ⊆ T E`. | n/a — the image under an injective map, `Set.image_subset_image_iff` | `mathlib` |
| `Sec. III-B (complexity)` | `Prop. 1` is a mixed-integer quadratic program, in NP [15]; (14) is solvable in `O(m^{n-1})` for fixed rank [16]; the dual (18) is a semidefinite program of polynomial complexity [17]. | n/a — restated from Papadimitriou, Ferrez et al. and Vandenberghe and Boyd, none with a page here | `restated` |
| `Eq. 17` | `p* = max_{uᵢ² ≤ 1} uᵀ Gₜᵀ Gₜ u`, by `{u \| \|u\| ≤ 1} = {u \| uᵢ² ≤ 1}`. | n/a — `sq_le_one_iff_abs_le_one` | `mathlib` |
| `Lemma 3` | (Upper bound on the maximum zonotope norm) The dual `d* = min_{λ ≥ 0} 1ᵀ λ` s.t. `diag(λ) - GᵀG ≽ 0` has `d* ≥ ⌈Z⌉²` (Eq. 18). | [`MaxNormSqLeOfDual.lean`](../../src/CORALean/ContSet/Zonotope/Real/Theorems/MaxNormSqLeOfDual.lean) — every feasible `λ` bounds `⌈Z⌉²`, so the optimum does | `correct` |
| `Eq. 19` | (17) as a rank-one semidefinite program; dropping the rank constraint gives a relaxation whose dual is (18), with strong duality, so the gap between (17) and (18) is due to the rank constraint alone. | — | — |
| `Thm. 1` | (Enclosing ellipsoid) `E(r̂ E₀, z̄) ⊇ Z(G, z̄)` for `E₀` from (13) and `r̂ ≥ ⌈E₀^{-1/2} Z(G, z̄)⌉²` from `Lemma 3` (Eq. 20). | [`Zonotope_to_Ellipsoid.lean`](../../src/CORALean/ContSet/Conversion/Real/Zonotope_to_Ellipsoid.lean) — `Zonotope.ellipsoidNorm`, `ellipsoidNorm_contains`: shape `r F Fᵀ` for any invertible factor `F` of `E₀` and any `r ≥ ⌈F⁻¹ Z⌉²` | `correct` |
| `Example 1` | For the `G ∈ ℝ^{5×7}` of (21), `⌈Z⌉² = 231`, `d* = 233.250`, and [19] tightens the bound to `231.932`. | n/a — an illustration of the duality gap; the exact value was checked by enumerating the `2⁷` sign vectors, not in Lean | `not-a-claim` |
| `Sec. IV (uniform points)` | An exactly uniform distribution of `m` points on the sphere is impossible for arbitrary `m`, to the authors' knowledge; random, deterministic or partition-based points approximate it [21]-[23]. | n/a — a remark on the literature | `not-a-claim` |
| `Lemma 4` | ([23, Thm. 5.4.1] and [24, 3., Thm.] combined) Zonotopes `Z(S, z̄)` with the points of the sphere partition of [23] approximate a sphere in the Hausdorff distance at the rate `O(m^{-1/n})`. | n/a — restated from Leopardi's thesis and Linhart, neither with a page here | `restated` |
| `Thm. 2` | (Inscribed zonotope) `Z(r̂^{-1/2} T⁻¹ S, ē) ⊆ E(E, ē)` for `T = E^{-1/2}`, points `vᵢ` on the sphere and `r̂ ≥ ⌈Z(S, ·)⌉²` (Eqs. 22-24); `r̂` may be any upper bound (Remark a). | [`Ellipsoid_to_Zonotope.lean`](../../src/CORALean/ContSet/Conversion/Real/Ellipsoid_to_Zonotope.lean) — `Ellipsoid.zonotopeInnerNorm`, `contains_zonotopeInnerNorm`, for any points; the printed proof ends with `Z(r̂⁻¹ T⁻¹ S, ē)`, a typo for the statement's `r̂^{-1/2}` | `correct` |
| `Eq. 25` | The maximum-volume ellipsoid inscribed in `{A x ≤ b}`, `min -log det B` s.t. `‖B aᵢ‖₂ + aᵢᵀ z̄ ≤ bᵢ` [9, Sec. 8.4.2]. | n/a — restated from Boyd and Vandenberghe | `restated` |
| `Lemma 5` | (Lower bound on the squared minimum norm) If the test `ν eᵢ ∈ Z`, `i = 1, …, n`, of [14, Sec. 4.4] passes, then `l̂ = ν²/n` is a lower bound on `⌊Z⌋²` (Eq. 26); the test is the feasibility of `ν eᵢ = G x + z̄`, `x ∈ [-1, 1]ᵐ`. | [`BallSubsetOfAxisTest.lean`](../../src/CORALean/ContSet/Zonotope/Real/Theorems/BallSubsetOfAxisTest.lean), [`BallSubsetOfAxisTestCounterexample.lean`](../../src/CORALean/ContSet/Zonotope/Real/Theorems/BallSubsetOfAxisTestCounterexample.lean) — the test measured from the centre, `z̄ + ν eᵢ ∈ Z`; the counterexample `[5, 7]`, `ν = 6` **Counterexample:** `Zonotope.ball_subset_of_axis_test_counterexample` | `fixed` — as printed the test checks `ν eᵢ` itself, which bounds nothing for a zonotope off the origin; true from the centre; see Findings |
| `Sec. V (complexity)` | The test of `Lemma 5` costs `O(n lp)`, `lp` the cost of a linear-programming feasibility check. | — | — |
| `Thm. 3` | (Inscribed ellipsoid) `E(l̂ E₀, z̄) ⊆ Z(G, z̄)` for `E₀ = G Gᵀ` and `l̂ ≤ ⌊E₀^{-1/2} Z(G, z̄)⌋²` from `Lemma 5` (Eq. 27). | [`Zonotope_to_Ellipsoid.lean`](../../src/CORALean/ContSet/Conversion/Real/Zonotope_to_Ellipsoid.lean) — `Zonotope.ellipsoidInnerNorm`, `contains_ellipsoidInnerNorm`: for any invertible factor `F` of `E₀` and `l̂` a ball of radius `√l̂` inside `F⁻¹ Z` around its centre | `correct` |
| `Thm. 4` | (Enclosing zonotope) `E(E, ē) ⊆ Z(l̂^{-1/2} T⁻¹ S, ē)` for `T = E^{-1/2}`, points on the sphere and `l̂ ≤ ⌊Z(S, ·)⌋²` (Eqs. 28-30). | [`Ellipsoid_to_Zonotope.lean`](../../src/CORALean/ContSet/Conversion/Real/Ellipsoid_to_Zonotope.lean) — `Ellipsoid.zonotopeNorm`, `zonotopeNorm_contains`, for any points with a ball of radius `√l̂` inside `Z(S, 0)` | `correct` |
| `Sec. VI` | Volume ratios and run times of `Thm. 1` and `Thm. 3` against the optimal ellipsoids (11) and (25) on random zonotopes (Tables I-II). | n/a — an experiment | `not-a-claim` |

## Findings

**`Def. 4` — normalized rows.** `⌊Z⌋² = min(b²)` is the squared radius of the largest ball around
the centre only when every row of `A` has unit length; scaling a row by `2` doubles its `bᵢ` and
leaves the set alone. The derivation (7)-(10) assumes it ("if we assume that `aᵢ` is normed"), and
CORA's `minnorm` gets normalized rows from `zonotope/polytope`; the definition does not say so. [`IsGreatestBallRadius.lean`](../../src/CORALean/ContSet/HPolytope/Real/Theorems/IsGreatestBallRadius.lean)

**`Lemma 5` — the test points.** The lemma asks for `ν eᵢ ∈ Z`, and the paragraph after it checks
the feasibility of `ν eᵢ = G x + z̄`: the points `ν eᵢ` themselves, not `z̄ + ν eᵢ`. For
`Z = [5, 7]` and `ν = 6` the test passes (`6 ∈ Z`) while `⌊Z⌋² = 1 < 36 = ν²/n`. Measured from the
centre the lemma holds, and `Thm. 3` needs that reading: it applies the lemma to
`E₀^{-1/2} Z(G, z̄)`, centred at `E₀^{-1/2} z̄`. The proof also calls the hull of the points
`±ν eᵢ` a rotated hypercube, which it is only for `n ≤ 2`; it is a cross-polytope, and the radius
`ν/√n` of its inscribed ball is the one the lemma states. CORA does not implement the test
(`zonotope/ellipsoid.m`: "we do not implement the test used to compute the necessary lower bound"). [`BallSubsetOfAxisTest.lean`](../../src/CORALean/ContSet/Zonotope/Real/Theorems/BallSubsetOfAxisTest.lean), [`BallSubsetOfAxisTestCounterexample.lean`](../../src/CORALean/ContSet/Zonotope/Real/Theorems/BallSubsetOfAxisTestCounterexample.lean)
