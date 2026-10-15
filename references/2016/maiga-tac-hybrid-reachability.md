# A Comprehensive Method for Reachability Analysis of Uncertain Nonlinear Hybrid Systems

M. Maïga, N. Ramdani, L. Travé-Massuyès and C. Combastel. "A Comprehensive Method for Reachability Analysis of Uncertain Nonlinear Hybrid Systems". IEEE Transactions on Automatic Control, 61(9):2341-2356, 2016.

**Source:** https://hal.science/hal-01650701v1/file/IEEE_TAC_postprint.pdf (the authors' accepted manuscript, deposited on HAL; its running head says "accepted for publication ... has not been fully edited"; all 17 pages read in full, text extracted with `pypdf`; the typeset IEEE version, <https://doi.org/10.1109/TAC.2015.2491740>, was not reachable)  
**Inventory:** unconfirmed (against the accepted manuscript; the typeset version may number or word its items differently. The manuscript's numbered items are Props. 3.1, 3.2, 4.1, 4.2, 6.1, 7.1, Thms. 1-4, Def. 1, Algs. 1-6 and Remarks 1-3)

CORA's default `enclosePoints` method (`'maiga'`) is this paper's `cloud2zonotope` (Alg. 3, Alg. 4) run for a
grid of compression ratios, the zonotope of least size kept (Alg. 5). The rest of the paper, the interval-Taylor
integrator with Lohner's QR factorization, the flow/guard intersection and the reset map of a hybrid automaton,
is not what CORA's reachability runs and is `not-covered`. What is formalized is the part CORA relies on:
the enclosure of a point cloud by the zonotope of Alg. 3 (every point lies in it, for any principal direction and
any ratio), the merge of a list of solution domains by Alg. 5 (every domain lies in the result) and the convexity
argument behind it (Prop. 6.1, Thm. 4). The principal direction, `svd(X)(:, 1)`, has no algorithm in the
library, so it is an argument and the zonotope is CORA's for that direction. CORA's `aux_enclosePointsMaiga`
differs from Alg. 5 in using 100 ratios `i/100` and the size of eq. 46, and is `Zonotope.enclosePointsMaiga`.

## Results

| Result | What it says | In CORALean | Class |
|---|---|---|---|
| `Prop. 3.1` | The Minkowski sum of two zonotopes Z₁ = c₁ ⊕ R₁B^{p₁} and Z₂ = c₂ ⊕ R₂B^{p₂} is the zonotope Z₁ + Z₂ = (c₁ + c₂) ⊕ [R₁ R₂]B^{p₁+p₂}. | n/a — restated; tracked as `Sec. 2` on [Girard 2005](../2005/girard-hscc-reachability-zonotopes.md) | `restated` |
| `Prop. 3.2` | The image of a zonotope Z = c ⊕ RB^p by a linear map L is LZ = Lc ⊕ (LR)B^p. | n/a — restated; tracked as `Sec. 2` on [Girard 2005](../2005/girard-hscc-reachability-zonotopes.md) | `restated` |
| `Thm. 1` | (Inclusion of a family of zonotopes, from [66]) For c ∈ ℝⁿ and an interval matrix [M] ∈ 𝕀ℝ^{n×p}, the family c ⊕ [M]B^p lies in ♦(Z) = c ⊕ JB^{p+n}, J = [mid([M]) \| G], G diagonal with G_ii = Σ_{j=1}^{m} rad([M]_ij) (eqs. 11-12; m is not defined, p is meant). | n/a — restated; tracked as `Thm. 4` on [Alamo et al. 2005](../2005/alamo-automatica-guaranteed-estimation.md) | `restated` |
| `Thm. 2` | (Zonotope extension, from [66], [68]) For F: ℝⁿ → ℝⁿ with continuous derivatives, a zonotope Z = c ⊕ RB^p and [M] ∈ 𝕀ℝ^{n×p}: ∇F(Z)R ⊆ [M] ⇒ F(Z) ⊆ F(c) ⊕ ♦([M]B^p). | n/a — restated; tracked as `Thm. 5` on [Alamo et al. 2005](../2005/alamo-automatica-guaranteed-estimation.md), the same inclusion without the disturbance `W` | `restated` |
| `Alg. 1` | (Interval-Solve) Branch and prune for the constraint system ∧ hᵢ(z) = 0 over a box: bisect a box unless some hᵢ excludes 0 (discard) or the box or its residual is small (store). | n/a — a constraint-satisfaction solver for the flow/guard intersection of a hybrid automaton, which CORA's reachability does not run | `not-covered` |
| `Alg. 2` | (ϕQR) The interval-Taylor step with Lohner's QR factorization: [v](t), [S](t), [q](t), [z](t), A(t) from QR of mid([S](t)A_j), [r](t). | n/a — guaranteed set integration by Lohner's method, which CORA's `nonlinearSys` does not use (it linearizes or polynomializes conservatively) | `not-covered` |
| `Prop. 4.1` | (Conservative polynomial interpolation) Eq. 13 is a conservative interpolation, an analytical solution of the flow-pipe for t ∈ [t_j, t_{j+1}], since f^{[k]}([z̃_j]) encloses the Taylor remainder. | n/a — a property of Alg. 2, see there | `not-covered` |
| `Prop. 4.2` | The solution domain Z(t) = A(t)[r](t) ⊕ [v](t) (an MSPB: parallelotope plus axis-aligned box) is the zonotope c(t) ⊕ R(t)B^{2n} with c = A mid([r]) + mid([v]) and R = [A dr([r]) \| dr([v])], dr(·) = diag(rad(·)) (eqs. 17-20). | [`MspbSetExact.lean`](../../src/CORALean/ContSet/Zonotope/Real/Theorems/MspbSetExact.lean) — the zonotope `(A □[r]) ⊕ □[v]` of `Interval.zonotope`, whose centre and generators are `mid` and `diag(rad)`; for intervals with `inf ≤ sup`, as intervals are | `correct` |
| `Thm. 3` | (Nonlinear reset of an MSPB) For Z⋆ = A[r] + [v], ρ(Z⋆) ⊆ A′[r]′ + [v]′ with A′ the n first columns of the norm-sorted J̃, [r]′ = Bⁿ, [v]′ = ρ_e(c) + □(J̃(:, n+1:3n)B^{2n}), J = [mid([∇ρ_e]R) \| G] (eqs. 30-34). | n/a — the reset map of a hybrid transition, which this paper's Algorithm 6 applies | `not-covered` |
| `Alg. 6` | (Hybrid-Transition) Flow/guard intersection by bisection of the time interval with HC4-Revise, a reset by Thm. 3 and a merge of the frontier by Alg. 5. | n/a — hybrid-automaton transition handling with the CSP solver of Alg. 1 | `not-covered` |
| `Def. 1` | (Z±) For R ∈ ℝ^{n×p}, Z(R) = RB^p is the centred zonotope generated by R, and Z±(R) = {Rσ : σ ∈ {-1, 1}^p}, the image by R of the 2^p vertices of the unit cube (eq. 37). | [`SignedSums.lean`](../../src/CORALean/ContSet/Zonotope/Real/Operations/SignedSums.lean) — `Zonotope.signedSums`, the generators as a family of columns | `correct` |
| `Prop. 6.1` | (Containment property) For all R: V(Z(R)) ⊆ Z±(R) (38); C(Z±(R)) = Z(R) (39); and for p = 2n there is R_g with 2 card(V(Z(R))) ≤ card(V(Z±(R))) ≤ 2 card(V(Z(R_g))) (40), where V and C are the vertices and the convex hull. | — partial: [`ExtremePointsSubsetSignedSums.lean`](../../src/CORALean/ContSet/Zonotope/Real/Theorems/ExtremePointsSubsetSignedSums.lean) (38), [`ConvexHullSignedSums.lean`](../../src/CORALean/ContSet/Zonotope/Real/Theorems/ConvexHullSignedSums.lean) (39); missing: (40), which counts vertices and needs the maximal number 2Σ_{i<n} C(p-1, i) of vertices of a zonotope; see Findings | — |
| `Remark 3` | Z±([R₁, R₂]) = Z±(R₁) ⊕ Z±(R₂), so the point set P of eq. 41 is ⋃ₗ Aₗ[r]±ₗ ⊕ [v]±ₗ, with [r]±, [v]± the vertices of the two boxes. | [`SignedSumsAppend.lean`](../../src/CORALean/ContSet/Zonotope/Real/Theorems/SignedSumsAppend.lean), [`MspbOuter.lean`](../../src/CORALean/ContSet/Zonotope/Real/Theorems/MspbOuter.lean) — the first the identity, the second (`aux_corner_plus_map`) that the corners of `(A □[r]) ⊕ □[v]` are `A [r]± + [v]±` | `correct` |
| `Thm. 4` | Let M be convex, Z⋆′ₗ = cₗ ⊕ Z(Rₗ) the MSPBs and P = ⋃ₗ (cₗ + Z±(Rₗ)) (eq. 41). Then P ⊆ M ⇒ ⋃ₗ Z⋆′ₗ ⊆ M (eq. 42). | [`ConstructSubsetOfSignedSums.lean`](../../src/CORALean/ContSet/Zonotope/Real/Theorems/ConstructSubsetOfSignedSums.lean) — for any finite family of zonotopes, the MSPBs being the case of `2n` generators | `correct` |
| `Eq. 41` | P = ⋃_{l=1}^{L} (cₗ + Z±(Rₗ)), the point set whose enclosure by a convex set encloses the union of the MSPBs. | [`ConstructSubsetOfSignedSums.lean`](../../src/CORALean/ContSet/Zonotope/Real/Theorems/ConstructSubsetOfSignedSums.lean), [`SignedSums.lean`](../../src/CORALean/ContSet/Zonotope/Real/Operations/SignedSums.lean) | `correct` |
| `Alg. 3` | (cloud2zonotope) From the cloud X = {xᵢ}, ratio ∈ [0,1] and s₁, s₂: while (iter < s₁) ∨ (∃i radᵢ > s₂ wᵢ), centre X on the middle of its interval hull (minbox), take u the first left singular vector of X, g := ratio \|u · rad\| u, X := compress(X, g), c := c + mid, R := [R, g]; then c := c + mid, R := [R, diag(rad)] for the box of what is left. The result c ⊕ Z(R) contains all the points. | [`Cloud2zonotope.lean`](../../src/CORALean/ContSet/Zonotope/Real/Operations/Cloud2zonotope.lean), [`Cloud2zonotopeLoop.lean`](../../src/CORALean/ContSet/Zonotope/Real/Operations/Cloud2zonotopeLoop.lean), [`Cloud2zonotopeMem.lean`](../../src/CORALean/ContSet/Zonotope/Real/Theorems/Cloud2zonotopeMem.lean) — the zonotope for any direction oracle `dir` (the SVD has no algorithm here) and any `ratio`, and the loop continues while `iter < s₁ ∧ ∃i radᵢ > s₂ wᵢ`, as the text says; [`Cloud2zonotopeCoraZeroGenerator.lean`](../../src/CORALean/ContSet/Zonotope/Real/Counterexamples/Cloud2zonotopeCoraZeroGenerator.lean) | `underspecified` — the printed test is `∨`, with which `s₁ = n`, `s₂ = 0` does not stop after `n` rounds as Sec. VI-C says; `rad` is unassigned at the first test; step 8 cuts a zero generator from a cloud with extent (0/0 in step 2 of Alg. 4); see Findings |
| `Alg. 4` | (compress) With u = g/‖g‖, each point xᵢ is replaced by xᵢ - d u, d the coordinate xᵢ · u clamped to [-‖g‖, ‖g‖]. | [`Cloud2zonotopeCompress.lean`](../../src/CORALean/ContSet/Zonotope/Real/Operations/Cloud2zonotopeCompress.lean) | `underspecified` — u = g/‖g‖ is 0/0 at g = 0, which Alg. 5 reaches at ratio = 0 and step 8 of Alg. 3 at u · rad = 0; Lean's x/0 = 0 gives u = 0 and the identity |
| `Eq. 43` | X ⊂ X̄ ⊕ g[-1, +1], the compressed cloud X̄ with the segment re-added contains the cloud X. | [`Cloud2zonotopeCompressMem.lean`](../../src/CORALean/ContSet/Zonotope/Real/Theorems/Cloud2zonotopeCompressMem.lean) | `correct` |
| `Alg. 5` | (MSPB) Merge the solution domains of a list: P := ⋃ Aₗ[r]±ₗ ⊕ [v]±ₗ; for ratio = 0, 0.1, ..., 1 run cloud2zonotope(X_P, ratio, n, 0) and its size µ (eq. 45); take r* = argmin µ and return the MSPB (A, [r], [v]) of c ⊕ Z(R) at r*. | [`Mspb.lean`](../../src/CORALean/ContSet/Zonotope/Real/Operations/Mspb.lean), [`MspbOuter.lean`](../../src/CORALean/ContSet/Zonotope/Real/Theorems/MspbOuter.lean) — the zonotope `c ⊕ Z(R)` returned, its MSPB attributes being the centre and the `n` first and `n` last generators; every solution domain `A [r] + [v]` lies in it, for any `dir`; [`EnclosePointsMaiga.lean`](../../src/CORALean/ContSet/Zonotope/Real/Operations/EnclosePointsMaiga.lean), [`EnclosePointsMaigaMem.lean`](../../src/CORALean/ContSet/Zonotope/Real/Theorems/EnclosePointsMaigaMem.lean) for CORA's variant (100 ratios, size by eq. 46) | `underspecified` — the grid starts at ratio = 0, where g = 0 and Alg. 4 divides 0/0; ties in argmin are broken towards the first; the MSPB attributes are not split off; see Findings |
| `Eq. 44` | The optimal compression ratio is ratio* = argmin_{ratio ∈ [0,1]} µ(Z(R)); the text evaluates µ on a grid of ten values and takes the best. | — partial: [`Mspb.lean`](../../src/CORALean/ContSet/Zonotope/Real/Operations/Mspb.lean) (the least size over the grid of eleven ratios 0, 0.1, ..., 1); missing: the argmin over the whole interval [0, 1] | — |
| `Eq. 45` | The volume of Z(R) = RB^p, p ≥ n, is 2ⁿ Σ_{1 ≤ i₁ ≤ i₂ ≤ ... ≤ iₙ ≤ p} \|det[r_{i₁}, ..., r_{iₙ}]\|. | [`Volume.lean`](../../src/CORALean/ContSet/Zonotope/Real/Operations/Volume.lean) — `Zonotope.volume`, the sum over the `n`-subsets of generators | `underspecified` — the printed index range i₁ ≤ ... ≤ iₙ admits repeated generators, whose determinants vanish; the n-subsets (i₁ < ... < iₙ) supply the sum |
| `Eq. 46` | The segment-length size Sm(Z(R)) = Σ_{i=1}^{n} Σ_{i=1}^{p} R²_ij = ‖R‖²_F = Tr(RᵀR). | [`SegmentLength.lean`](../../src/CORALean/ContSet/Zonotope/Real/Operations/SegmentLength.lean) — `Zonotope.segmentLength` | `underspecified` — the inner index is printed i, j is meant |
| `Eq. 47` | The P-radius of Z = c ⊕ RB^p is Prad(Z) = max_{x ∈ Z} ‖x - c‖²_P = max (x - c)ᵀP(x - c), P = Pᵀ ≥ 0. | [`PRadius.lean`](../../src/CORALean/ContSet/Zonotope/Real/Definitions/PRadius.lean) — `Zonotope.pRadius`, the supremum | `correct` |
| `Prop. 7.1` | (Conservative hybrid reachability) The flow-pipe alternating Alg. 2, Alg. 6 and Alg. 5 encloses all trajectories of the hybrid automaton consistent with X₀ ⊆ ℝⁿ and P ⊆ ℝ^{n_p}; proved from Prop. 4.1, Thm. 3, Thm. 4 and the conservatism of the contractors. | n/a — the guarantee of the whole hybrid algorithm, whose other steps (Alg. 2, Alg. 6) are not covered; its trajectory-fusion step is `Alg. 5` | `not-covered` |
| `Sec. 7 (complexity)` | The cost of Alg. 5 is about m²2^{2n}(40n³ + 40n² + n) + 80n⁴ floating-point operations, of the vertex enumeration about m n 2^{2n}. | n/a — a running time | `not-a-claim` |
| `Remark 1` | Urgent semantics: the guard set triggers a transition as soon as it is hit, so invariants are optional. | n/a — a remark on the hybrid-automaton model | `not-a-claim` |
| `Remark 2` | Eq. 13 holds for any t in [t_j, t_{j+1}], an extension of the grid-point enclosures of guaranteed set integration, needed for the flow/guard intersection. | n/a — a remark on Alg. 2 | `not-a-claim` |

## Findings

**Alg. 3 — the step that cuts the generator.** Step 8 sets `g := ratio |u · rad| u` and the text calls
its length "a fraction of (an approximation of) the largest projection of the points in the (centered) cloud
along u", computed "by the scalar product u · rad". `u · rad` is signed in `u`: for the cloud
`{(1, -1), (-1, 1)}` the first principal direction is `u = (1, -1)/√2`, which carries the whole cloud
(`Σⱼ (u · xⱼ)² = Σⱼ ‖xⱼ‖² = 4`), but `rad = (1, 1)`, so `u · rad = 0` and `g = 0` for every ratio. Step 2 of
`compress` is then `u = g/‖g‖ = 0/0`. The largest projection is bounded by `|u| · rad` (componentwise absolute
value), not `|u · rad|`. CORA's `aux_cloud2zonotope` copies the step and divides `0/0` in MATLAB, so the points
become `NaN` (read from the source, not run); see [`zonotope` `enclosePoints`](../coverage/contSet/zonotope.md). The same `0/0` is reached
whenever the cloud is a single point (`rad = 0`) and, in Alg. 5, at `ratio = 0`, the first value of the printed
grid. Lean's `x/0 = 0` makes `cloud2zonotopeCompress` the identity at `g = 0`, so the formalized
algorithm is total, and encloses all the same (`Zonotope.cloud2zonotope_mem`); it simply does not compress.
[`Cloud2zonotopeCoraZeroGenerator.lean`](../../src/CORALean/ContSet/Zonotope/Real/Counterexamples/Cloud2zonotopeCoraZeroGenerator.lean), [`Cloud2zonotopeCompress.lean`](../../src/CORALean/ContSet/Zonotope/Real/Operations/Cloud2zonotopeCompress.lean)

**Alg. 3 — the loop test.** The listing reads `while (iter < s₁) ∨ (∃i radᵢ > s₂ wᵢ)`, but Sec. VI-B says the
loop runs "until one of the two stopping criteria s₁ or s₂ are satisfied" and Sec. VI-C that `s₁ = n`, `s₂ = 0`
"yields an MSPB since there are exactly n compression iterations". With `∨` the loop ends only when both are
satisfied: for `s₂ = 0` when `rad = 0`, which compression does not reach in `n` rounds. It is read as `∧`. Its
test also reads `rad`, assigned in step 4 of the previous round, before the first round has assigned it; the first
round is taken unconditionally here. CORA ignores `s₂` altogether (the test is commented out) and runs exactly
`s₁ = n` rounds. [`Cloud2zonotopeLoop.lean`](../../src/CORALean/ContSet/Zonotope/Real/Operations/Cloud2zonotopeLoop.lean)

**Prop. 6.1, eq. 40.** Read literally, `2 card V(Z(R)) ≤ card V(Z±(R))` has `V(Z±(R))` the vertices of the
finite set `Z±(R)`, which by eq. 39 are those of `Z(R)`; the inequality is then false for every `R` with a
vertex. The text beneath ("`Z±(R)` only contains twice more points than the true number of vertices") shows that
`card Z±(R)` is meant, `2^p` for the `2^p` sign choices. Counted as a set it fails as well when sums coincide: `n = 1`,
`R = (1, 1)` has `Z(R) = [-2, 2]` with two vertices, but `Z±(R) = {-2, 0, 2}` has three points and `4 ≤ 3` is false.
With the sign choices counted with multiplicity the claim is the vertex bound `card V(Z(R)) ≤ 2^{p-1}`.
Eq. 40 is left unformalized; (38) and (39) are proved.

**Eqs. 45-46, Thm. 1.** Eq. 45 sums over `i₁ ≤ ... ≤ iₙ`, where repeated indices contribute determinants of zero
(`i₁ < ... < iₙ` is meant, as `Zonotope.volume` sums). Eq. 46 prints both summation indices as `i`. Thm. 1's `G_ii = Σ_{j=1}^{m}`
should run to `p`, the number of columns of `[M]`. None changes a result.

**CORA.** `enclosePoints.m` cites the paper as "TAC 2017"; it is IEEE TAC 61(9), 2016. Its `aux_enclosePointsMaiga`
minimises the size of eq. 46 over 100 ratios `i/100`, `i = 1, ..., 100`, where Alg. 5 minimises the volume of eq. 45 over
`0, 0.1, ..., 1`: the paper lists volume, segment length and P-radius as admissible sizes. Starting at `i = 1` avoids the
`0/0` of `ratio = 0`.
