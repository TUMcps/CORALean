# Scalable Zonotopic Under-approximation of Backward Reachable Sets for Uncertain Linear Systems

L. Yang and N. Ozay. "Scalable zonotopic under-approximation of backward reachable sets for uncertain linear systems". IEEE Control Systems Letters, 6:1555-1560, 2022.

**Source:** https://arxiv.org/pdf/2107.01724v3 (arXiv v3, 15 Apr 2022, the authors' version after publication, 8 pages, read in full; text extracted with `pypdf`, and the over- and underlines the extraction drops read from the arXiv LaTeX source of the same version). Volume and pages from the published record (doi:10.1109/LCSYS.2021.3123228); the typeset article was not reachable. CORA cites the paper in `contSet/@zonotope/reduceUnderApprox.m` (method `'yang'`) without a result number.  
**Inventory:** confirmed (Lemmas 1-2, Definition 1, Propositions 1-6, equations (1)-(20) and the tagged problems (min-out) and (max-in); the rows below are the results and the numbered displays that make a claim)

Inner (and outer) approximations of the robust backward reachable sets of `x⁺ = Ax + Bu + Ew + K`
by zonotopes. The Minkowski difference `Z ⊖ EW` of each step is approximated by subtracting a
zonotope *aligned* with `Z` — `Z`'s generators scaled by `αᵢ ∈ [0, 1]` — which is exact
generator-wise (`Prop. 3`); a linear program puts one around `EW` (`Prop. 1`), giving an inner
approximation of the difference, and another one inside `EW` (`Prop. 2`), giving an outer one.
`Prop. 5` runs the step backwards, and `Prop. 6` reduces the order by combining generator pairs,
CORA's `reduceUnderApprox(Z, 'yang', order)`. Formalized: all of it, the programs' solutions as
hypotheses. `Prop. 2` uses `W`'s halfspaces where its conclusion needs `EW`'s, which breaks it and
the outer halves of `Prop. 4` and `Prop. 5`; (16) states an equality where only `⊇` holds.

## Results

| Result | What it says | In CORALean | Class |
|---|---|---|---|
| `Lemma 1(i)` | X ⊖ Y ⊕ Z ⊆ X ⊕ Z ⊖ Y; in particular X ⊖ Y ⊕ Y ⊆ X ⊆ X ⊕ Y ⊖ Y. | n/a — restated from Li's thesis [16, Prop. 3.1] and the authors' CDC 2020 paper [25, Lemma 4]; `minkowskiDiff_add_subset_add` and `minkowskiDiff_add_subset` have it | `restated` |
| `Lemma 1(ii)` | For X, Y, Z convex, compact and nonempty, X ⊕ Z = Y ⊕ Z implies X = Y. | n/a — restated from Montejano 1996 [22]; `radstrom_cancel_eq` has it | `restated` |
| `Lemma 1(iii)` | For X, Y convex, compact and nonempty, X ⊕ Y ⊖ Y = X. | [`MinkowskiDiffAddCancel.lean`](../../src/CORALean/ContSet/ContSet/Theorems/MinkowskiDiffAddCancel.lean) — `X` convex and closed, `Y` nonempty and bounded | `correct` |
| `Lemma 2` | For Z = (G, c): Z = ⊕ᵢ({gᵢ}, cᵢ) with Σcᵢ = c; AZ = (AG, Ac); Z ⊕ Z' = ([G, G'], c + c'). | n/a — restated from Girard 2005 [8] | `restated` |
| `Eq. 2` | (k-step backward reachable set) X_{k+1} = {x \| ∃u ∈ U: ∀w ∈ W: Ax + Bu + Ew + K ∈ X_k}. | [`BackReachSetRobustExact.lean`](../../src/CORALean/ContDynamics/LinearSysDT/Definitions/BackReachSetRobustExact.lean) — `LinearSysDT.backReachSetRobustExact`, the matrices as arguments | `correct` |
| `Eq. 3` | For polytopes U, W, X₀: X_{k+1} = Proj_x({(x, u) \| u ∈ U, ∀wⱼ ∈ V_W: Ax + Bu + Ewⱼ ∈ X_k}). | n/a — restated from Smith, Nilsson and Ozay 2016 [24, Prop. 1] (the printed display drops `+ K`) | `restated` |
| `Eq. 4` | X_{k+1} = {x \| Ax ∈ X_k ⊖ EW ⊕ -BU - K}. | n/a — restated from Kurzhanskiy and Varaiya 2011 [14]; `LinearSysDT.backReachSetRobustExact_succ` has it, as a preimage under `A` | `restated` |
| `Def. 1` | (Aligned zonotope) Z' = (G', c') is aligned with Z = (G, c) if G' = [α₁g₁, …, α_N g_N] for some αᵢ ∈ [0, 1]. | [`Aligned.lean`](../../src/CORALean/ContSet/Zonotope/Real/Operations/Aligned.lean) — `Zonotope.aligned Z c α`; `αᵢ ∈ [0, 1]` is a hypothesis of the theorems that need it | `correct` |
| `Eq. 5` | (min-out) has O(MN + n_x) variables and O(M(N + n_x)) constraints. | n/a — computational complexity, a subject CORALean does not cover | `not-covered` |
| `Prop. 1` | For the minimizer (θ, ᾱ, c̄) of (min-out) — min Σbᵢαᵢ s.t. c + Σθᵢⱼgᵢ = Ewⱼ at every vertex wⱼ, \|θᵢⱼ\| ≤ αᵢ ≤ 1 — EW ⊆ Z̄(Z, EW) = ([ᾱ₁g₁, …, ᾱ_N g_N], c̄). | [`ImageSubsetAlignedOfMinOut.lean`](../../src/CORALean/ContSet/Zonotope/Real/Theorems/ImageSubsetAlignedOfMinOut.lean) — at any feasible point, W the convex hull of its vertices | `underspecified` — (min-out) ranges its constraint over `i = 0, 1, …, N`; there is no `g₀`, read as `1, …, N` |
| `Eq. 6` | (max-in) has O(N + n_x) variables and O(N + L) constraints. | n/a — computational complexity, a subject CORALean does not cover | `not-covered` |
| `Prop. 2` | For the maximizer (α̲, c̲) of (max-in) — max Σdᵢlog αᵢ s.t. Hc + \|HG\|α ≤ h, 0 ≤ α ≤ 1, (H, h) the H-representation of W — Z̲(Z, EW) = ([α̲₁g₁, …, α̲_N g_N], c̲) ⊆ EW. | [`AlignedSubsetOfMaxIn.lean`](../../src/CORALean/ContSet/Zonotope/Real/Theorems/AlignedSubsetOfMaxIn.lean), [`AlignedSubsetOfMaxIn.lean`](../../src/CORALean/ContSet/Zonotope/Real/Counterexamples/AlignedSubsetOfMaxIn.lean) — the inclusion in `{x \| Hx ≤ h}` at any feasible point, and a maximizer with `W`'s halfspaces not inside `EW` **Counterexample:** `Zonotope.aligned_subset_of_maxIn_counterexample` | `fixed` — (max-in) is built from `W`'s halfspaces, which bound the zonotope inside `W`, not `EW`: false at `E = ½`, `W = Z = [-1, 1]`; true with `EW`'s halfspaces; see Findings |
| `Prop. 3` | For Z' = (G', c') aligned with Z = (G, c): Z ⊖ Z' = ([(1 - α₁)g₁, …, (1 - α_N)g_N], c - c'). | [`MinkDiffAlignedExact.lean`](../../src/CORALean/ContSet/Zonotope/Real/Theorems/MinkDiffAlignedExact.lean) — `Zonotope.minkDiffAligned_exact`, which is also Althoff 2015's `Prop. 5` | `correct` |
| `Prop. 4` | Z ⊖ Z̄(Z, EW) ⊆ Z ⊖ EW ⊆ Z ⊖ Z̲(Z, EW), both computed by generator-wise subtraction. | [`MinkDiffAlignedBounds.lean`](../../src/CORALean/ContSet/Zonotope/Real/Theorems/MinkDiffAlignedBounds.lean) — for aligned zonotopes around and inside any set; [`MinkDiffAlignedBounds.lean`](../../src/CORALean/ContSet/Zonotope/Real/Counterexamples/MinkDiffAlignedBounds.lean) — `Z ⊖ EW = [-½, ½]` is not inside `Z ⊖ Z̲ = {0}` at `W = Z = [-1, 1]`, `E = ½` **Counterexample:** `Zonotope.minkDiffAligned_bounds_counterexample` | `fixed` — the right inclusion inherits `Prop. 2`'s use of `W`'s halfspaces and fails with them (`Z ⊖ EW = [-½, ½] ⊄ Z ⊖ Z̲ = {0}` on its counterexample); true with `EW`'s |
| `Eq. 12` | (11)-(13): Z̲₀ = Z̄₀ = Z₀, Z̲_{k+1} = A⁻¹(Z̲_k ⊖ Z̄(Z̲_k, EW) ⊕ -BU - K), Z̄_{k+1} = A⁻¹(Z̄_k ⊖ Z̲(Z̄_k, EW) ⊕ -BU - K). | [`BackReachAligned.lean`](../../src/CORALean/ContSet/Zonotope/Real/Operations/BackReachAligned.lean) — one recursion, the aligned zonotope's center and scalings a parameter: (min-out)'s for (12), (max-in)'s for (13) | `correct` |
| `Prop. 5` | For X_k from (2) and Z̲_k, Z̄_k from (11)-(13): Z̲_k ⊆ X_k ⊆ Z̄_k. | [`BackReachAlignedInner.lean`](../../src/CORALean/ContDynamics/LinearSysDT/Theorems/Real/BackReachAlignedInner.lean), [`BackReachAlignedOuter.lean`](../../src/CORALean/ContDynamics/LinearSysDT/Theorems/Real/BackReachAlignedOuter.lean), [`MemBackReachAlignedSuccIff.lean`](../../src/CORALean/ContSet/Zonotope/Real/Theorems/MemBackReachAlignedSuccIff.lean), [`BackReachSetRobustExactSucc.lean`](../../src/CORALean/ContDynamics/LinearSysDT/Theorems/Real/BackReachSetRobustExactSucc.lean), [`BackReachAlignedOuter.lean`](../../src/CORALean/ContDynamics/LinearSysDT/Counterexamples/Real/BackReachAlignedOuter.lean) — `A` invertible (A3), each step's aligned zonotope around `EW` (inner half) or inside `EW` (outer half), scalings in `[0, 1]` **Counterexample:** `LinearSysDT.backReachAligned_outer_counterexample` | `fixed` — the outer half inherits `Prop. 2`'s use of `W`'s halfspaces: at `A = 1`, `B = 0`, `K = 0` on its counterexample `X₁ = [-½, ½] ⊄ Z̄₁ = {0}`; true with `EW`'s |
| `Sec. IV-B` | N_{k+1} = N_k + N_U: each step adds U's generator count. | [`BackReachAlignedH.lean`](../../src/CORALean/ContSet/Zonotope/Real/Complexity/Space/Theorems/BackReachAlignedH.lean) — `Zonotope.backReachAligned_h` | `correct` |
| `Prop. 6` | Replacing two columns gᵢ, gⱼ of G by gᵢ + gⱼ (G₁) or gᵢ - gⱼ (G₂) gives (G₁, c) ⊆ (G, c) and (G₂, c) ⊆ (G, c). | [`CombineGens.lean`](../../src/CORALean/ContSet/Zonotope/Real/Operations/CombineGens.lean), [`CombineGensInner.lean`](../../src/CORALean/ContSet/Zonotope/Real/Theorems/CombineGensInner.lean) | `correct` |
| `Sec. IV-B.1` | (Order reduction) Replace two generators by their combination until the order is small enough. | [`ReduceUnderApproxYang.lean`](../../src/CORALean/ContSet/Zonotope/Real/Operations/ReduceUnderApproxYang.lean), [`ReduceUnderApproxYangInner.lean`](../../src/CORALean/ContSet/Zonotope/Real/Theorems/ReduceUnderApproxYangInner.lean) — down to `N` generators, the choice of pair and sign a parameter | `correct` |
| `Eq. 15` | (Heuristic) Combine the pair minimizing ‖gᵢ‖₂‖gⱼ - ĝᵢgⱼᵀĝᵢ‖₂, with gᵢ + gⱼ if ‖(gᵢ + gⱼ)ᵀG'‖₂ ≥ ‖(gᵢ - gⱼ)ᵀG'‖₂, else gᵢ - gⱼ. | n/a — a selection heuristic; `Prop. 6` holds for every choice, and `reduceUnderApproxYang` takes the choice as a parameter | `not-a-claim` |
| `Eq. 16` | For x ∈ Z̲_{k+1} some u ∈ U(x, Z̲_k) = {u ∈ U \| ∀w ∈ W: Ax + Bu + Ew + K ∈ Z̲_k} exists, and U(x, Z̲_k) = Proj_u{(u, θ) \| Ax + Bu + K = c⁽ᵏ⁾ + Σθᵢgᵢ⁽ᵏ⁾, u ∈ U, θ ∈ [-1, 1]}, (G⁽ᵏ⁾, c⁽ᵏ⁾) the G-rep of Z̲_k ⊖ Z̄(Z̲_k, EW). | [`BackReachAlignedControl.lean`](../../src/CORALean/ContDynamics/LinearSysDT/Theorems/Real/BackReachAlignedControl.lean), [`MinkowskiDiffNotSubsetMinkDiffAligned.lean`](../../src/CORALean/ContSet/Zonotope/Real/Theorems/MinkowskiDiffNotSubsetMinkDiffAligned.lean) — the existence and `⊇`, and a hexagon and triangle where every aligned zonotope around the triangle loses part of the difference **Counterexample:** `Zonotope.minkowskiDiff_not_subset_minkDiffAligned` **Counterexample:** `Zonotope.minkowskiDiff_not_subset_minkDiffAligned` | `fixed` — the two sets are not equal, only the projection is inside `U(x, Z̲_k)`, which is what finding one input needs; see Findings |
| `Sec. IV-B.2` | (Feedback) From x₀ ∈ Z̲_k, applying u_t ∈ U(x_t, Z̲_{k-t-1}) drives the state into Z̲₀ = Z₀ in exactly k steps, regardless of the disturbance. | [`BackReachAlignedFeedback.lean`](../../src/CORALean/ContDynamics/LinearSysDT/Theorems/Real/BackReachAlignedFeedback.lean) — some feedback exists with these inputs, and every closed-loop run reaches `Z₀` | `correct` |
| `Eq. 17` | For W = (G_W, c_W), a feasible point of max Σαᵢ s.t. [G_Z diag(α), EG_W] = G_ZΓ, c_Z - (c + Ec_W) = G_Zγ, ‖[Γ, γ]‖∞ ≤ 1, 0 ≤ α ≤ 1 gives (G_Z diag(α), c) ⊆ Z ⊖ EW. | [`AlignedSubsetMinkowskiDiffOfCert.lean`](../../src/CORALean/ContSet/Zonotope/Real/Theorems/AlignedSubsetMinkowskiDiffOfCert.lean) — through Sadraddini and Tedrake's `Thm. 3` | `correct` |
| `Eq. 18` | (17) has O(N(N + N_W) + n_x) variables and O(N + n_x) constraints. | n/a — computational complexity, a subject CORALean does not cover | `not-covered` |
| `Sec. V-A` | Comparison with Althoff's and Sadraddini's methods on random instances: times (Fig. 1) and volume ratios. | n/a — experiments | `not-a-claim` |
| `Sec. V-B` | Order reduction on random zonotopes: time and volume ratio (Fig. 2). | n/a — experiments | `not-a-claim` |
| `Sec. VI` | Case studies: aircraft position control and a double integrator with an uncontrollable subspace (Figs. 3-6). | n/a — experiments | `not-a-claim` |

## Findings

**`Prop. 2` — `W`'s halfspaces where `EW`'s are needed.** (max-in) is formulated with "the H-rep
`(H, h)` of the disturbance set `W`", and the proof shows `H(c̲ + Σθᵢα̲ᵢgᵢ) ≤ h`, i.e. the aligned
zonotope lies in `W`, then concludes it lies in `EW`. The two agree only for `E = I` (as in the
case studies); in general the constraint is not even well-typed (`H` acts on `ℝ^{n_w}`, `c` and
`gᵢ` live in `ℝ^{n_x}`). In one dimension with `W = [-1, 1]`, `E = ½` and `Z = [-1, 1]`, the
maximizer is `α = 1`, `c = 0`, so `Z̲ = [-1, 1] ⊄ EW = [-½, ½]`
(`aligned_subset_of_maxIn_counterexample`). With the H-representation of `EW` — `(HE⁻¹, h)` for
invertible `E` — the proposition holds as proved (`aligned_subset_of_maxIn`). The outer half of
`Prop. 4` and of `Prop. 5` rest on it: on the same instance `Z ⊖ Z̲ = {0}` misses
`Z ⊖ EW = [-½, ½]`, and with `A = 1`, `B = 0`, `K = 0`, `X₀ = Z` the first step of (13) gives
`Z̄₁ = {0}` against `X₁ = [-½, ½]`. The inner halves, which use (min-out), are unaffected.

**`Eq. 16` — an equality that is only `⊇`.** The projection replaces `Z̲_k ⊖ EW` by
`Z̲_k ⊖ Z̄(Z̲_k, EW)`, which `Prop. 4` shows is a subset; it is a proper one in general, whatever
weights (min-out) is solved with. For the hexagon with generators `(1, 0)`, `(0, 1)`, `(1, 1)` and
`EW` the triangle `(0, 0)`, `(1, 0)`, `(1, 1)`, a centrally symmetric aligned zonotope cannot match
the triangle's extent in all three facet directions, and one of four points of `Z ⊖ EW` is
always lost (`Zonotope.minkowskiDiff_not_subset_minkDiffAligned`); at `A = B = E = I`, `K = 0`,
`x = 0`, `U = Z` that point is in `U(x, Z̲_k)` and not in the projection. What the section uses —
an input from the projection is in `U(x, Z̲_k)`, and one exists for `x ∈ Z̲_{k+1}` — holds
(`backReachAligned_control`).
