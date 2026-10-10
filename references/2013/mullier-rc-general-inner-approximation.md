# General Inner Approximation of Vector-valued Functions

O. Mullier, É. Goubault, M. Kieffer and S. Putot. "General Inner Approximation of Vector-valued Functions". Reliable Computing, 18:117-143, 2013.

**Source:** https://reliable-computing.org/reliable-computing-18-pp-117-143.pdf (the journal's open-access PDF, pp. 117-143, 27 pages, read in full; text extracted with `pypdf`). CORA cites the paper in `contSet/@polyZonotope/innerApprox.m`, `contSet/@polyZonotope/contains_.m` and `global/functions/helper/sets/contSet/polyZonotope/innerApproxImage.m`, whose `aux_InnerGeneral` is `Alg. 3` and whose `aux_preconditionMatrix` is the preconditioner of (10).  
**Inventory:** confirmed (Corollary 2.1; Theorem 3.1, Lemma 3.1, Corollary 3.1, Example 3.2; Example 4.1, Definitions 4.2-4.5, 4.7, 4.8, Theorems 4.6, 4.9, 4.10, Remarks 4.1-4.2; Algorithms 1-4; equations (1)-(20); numbered per section)

Inner approximations of the range of `f : ℝᵐ → ℝⁿ` of rank `r`, by Goldsztejn and Jaulin's
interval test (`Cor. 2.1`) extended to the first `r` components: a submersion maps no
interior point onto the frontier of its image (`Lemma 3.1`), so a box the image of `∂u` misses
and that meets the image is inside it (`Thm. 3.1`), and a Hansen–Sengupta-type inclusion
proves that (`Cor. 3.1`), also preconditioned (`Eq. 10`). Formalized, without Brouwer's
theorem: the test's step from (5) to condition (i) does not hold on the faces of `∂u` where
only `u₂` is at a bound, but the corollary does, through the slice at `ũ₂`; with it, the
closed inclusion `Alg. 3` and CORA check. Sec. 4.3 extracts
a regular sub-matrix of the interval Jacobian by linear programs over binary picks; (14), (15),
(17) and (18) are sound, the printed (13) is infeasible and the printed (16) has the sign of
`μ` wrong.

## Results

| Result | What it says | In CORALean | Class |
|---|---|---|---|
| `Cor. 2.1` | For `f : x → ℝⁿ`, `J ∋ f'(x)` on `x`, `0 ∉ Jᵢᵢ`, `f(x̃) ∈ y`: `H(J, x̃, x, y) = x̃ + Diag⁻¹J (y - f(x̃) - OffDiag J (x - x̃)) ⊆ int(x)` (1) gives `y ⊆ range(f, x)`. | n/a — restated from Goldsztejn and Jaulin 2010 [5]; `Cor. 3.1` at `m = r` contains it, under (3) | `restated` |
| `Lemma 3.1` | For `f` `C¹` satisfying (3) and `E ⊂ D` compact, `∂(f₁:ᵣ(E)) ⊆ f₁:ᵣ(∂E)`. | [`SubmersionFrontier.lean`](../../src/CORALean/Global/SubmersionFrontier.lean) — `frontier_image_subset_image_frontier`, for a strict, surjective derivative at the interior points of `E`, which (3) gives | `correct` |
| `Thm. 3.1` | For `f` `C¹` satisfying (3), `u ⊂ D` a box and `y₁ ∈ IRʳ`: (i) `y₁ ∩ f₁:ᵣ(∂u) = ∅` and (ii) `f₁:ᵣ(ũ) ∈ y₁` for some `ũ ∈ u` give `y₁ ⊆ f₁:ᵣ(u)`. | [`InnerRangeOfFrontier.lean`](../../src/CORALean/Global/InnerRangeOfFrontier.lean) — `subset_image_of_disjoint_image_frontier`, `u` compact and `y₁` preconnected | `correct` |
| `Cor. 3.1` | For `f` satisfying (3), `u = (u₁, u₂)`, `f₁:ᵣ(ũ) ∈ y₁`, `J_{f₁:ᵣ} = (J₁ J₂)` enclosing the Jacobian on `u`, `0 ∉ (J₁)ᵢᵢ`: `H = ũ₁ + Diag⁻¹J₁ (y₁ - f₁:ᵣ(ũ) - OffDiag J₁ (u₁ - ũ₁) - J₂(u₂ - ũ₂)) ⊆ int(u₁)` (5) gives `y₁ ⊆ f₁:ᵣ(u)`. | [`InnerRangeTest.lean`](../../src/CORALean/Global/InnerRangeTest.lean), [`InnerTest.lean`](../../src/CORALean/Global/InnerTest.lean), [`InnerRangeTestStepCounterexample.lean`](../../src/CORALean/Global/InnerRangeTestStepCounterexample.lean) — `Icc_subset_image_of_innerTest`, (5) read over the real matrices in `J` and the points of `y₁` and `u` | `proof-gap` — the proof's step "(5) implies (i)" fails on faces of `∂u` with `u₂` at a bound (`innerTest_step_counterexample`); the corollary holds on the slice `v ↦ f₁:ᵣ(v, ũ₂)`; see Findings |
| `Example 3.2` | `f(x) = (sin 2x, sin x, x/2)` on `[0, π]` has rank 1; `Cor. 3.1` gives an inner range of one component, and no proper 2- or 3-dimensional box is in the range. | n/a — an illustration | `not-a-claim` |
| `Alg. 1` | (Range inner-approximation as defined in [5]) Bisect the domain until `Inner` accepts the box `ỹ = f(x̃) ∩ (f(mid x̃) + f'(x̃)(x̃ - mid x̃))` or the width falls below `ε`. | n/a — restated from Goldsztejn and Jaulin [5, Alg. 1]; its soundness is that of `Inner`, `Alg. 3` | `restated` |
| `Alg. 2` | (Inclusion test as defined in [5]) The test of `Cor. 2.1` with preconditioning and domain inflation. | n/a — restated from Goldsztejn and Jaulin [5, Alg. 2] | `restated` |
| `Example 4.1` | `f(x) = Ax`, `A = [1 1; -1 1]` on `[-2, 2]²`, inner approximation by `Alg. 1` (Fig. 3). | n/a — an illustration | `not-a-claim` |
| `Alg. 3` | (Inclusion test based on `Cor. 3.1`) Precondition `J_{f₁:ᵣ}` by `C`, split `u` into `(u₁, u₂)`, iterate `t = Diag⁻¹J₁ (y₁ - f₁:ᵣ(ũ) - OffDiag J₁(ũ₁ - ũ₁) - J₂(ũ₂ - ũ₂))` with domain inflation `ũ ← ũ + τt` while `ũ ⊆ u`, return true once `ũ + t ⊆ ũ`. | — partial: the acceptance test, not the loop. [`InnerRangeTestClosed.lean`](../../src/CORALean/Global/InnerRangeTestClosed.lean) (`Icc_subset_image_of_innerTest_closed`, `Cor. 3.1` with the closed inclusion `ũ + t ⊆ ũ` on which `Alg. 3` returns true, by Brouwer's theorem on the slice at `ũ₂`), which rests on `exists_mem_Icc_eq_add_of_jacobi`, the square case; missing: the domain-inflation loop with `τ` and `μ` and the preconditioned interval evaluation that feeds the test | — |
| `Eq. 10` | (Preconditioning) `C` the first `r` columns of `D_ũ⁻¹`, `D_ũ = (J_{f₁:ᵣ}(ũ); 0 Iₘ₋ᵣ)`, `C = (C₁, C₂)ᵀ`; the test of `Cor. 3.1` becomes `H_{f₁:ᵣ}(C J_{f₁:ᵣ}, ũ, u, C y₁) ⊆ int(u₁)`. | [`PreconditionedInnerTest.lean`](../../src/CORALean/Global/PreconditionedInnerTest.lean) — `Icc_subset_image_of_preconditioned_innerTest`, any `r × r` `C` with `det C ≠ 0`, against a box enclosing `C y₁` | `underspecified` — `C` as printed is `m × r` and `C J_{f₁:ᵣ}` is `m × m`; the test needs the `r × r` block `C₁ = J₁(ũ)⁻¹`, which CORA takes |
| `Def. 4.2` | (Regular interval matrix) `A` is regular iff every `A ∈ A` is nonsingular. | n/a — a definition; the theorems below state it as `det ≠ 0` for every real matrix in the bounds | `not-a-claim` |
| `Def. 4.3` | (Rank of an interval matrix) `A` has constant rank `r` iff its largest regular square sub-matrix is `r × r`; this means `rank A ≥ r` for every `A ∈ A`. | [`SubmatrixLp.lean`](../../src/CORALean/Global/SubmatrixLp.lean) — `le_rank_of_det_submatrix_ne_zero`: a regular `k × k` sub-matrix gives `rank A ≥ k` | `correct` |
| `Def. 4.4` | (Strictly diagonally dominant matrix) `\|aᵢᵢ\| > Σ_{j≠i} \|aᵢⱼ\|` (11). | n/a — a definition, Mathlib's hypothesis in `det_ne_zero_of_sum_row_lt_diag` | `not-a-claim` |
| `Def. 4.5` | (Strictly diagonally dominant interval matrix) `⟨aᵢᵢ⟩ > Σ_{j≠i} \|aᵢⱼ\|` (12), mignitude and magnitude. | n/a — a definition, the hypothesis of `isHMatrix_of_dominant` | `not-a-claim` |
| `Thm. 4.6` | (Lévy–Desplanques) A strictly diagonally dominant (interval) matrix is regular. | n/a — restated from Lévy 1881 and Taussky 1949 [14, 24]; Mathlib's `det_ne_zero_of_sum_row_lt_diag`, which `det_ne_zero_of_isHMatrix` uses | `mathlib` |
| `Eq. 13` | `max Σᵢⱼ xᵢⱼ` s.t. `Σᵢ xᵢⱼ ≤ 1`, `Σⱼ xᵢⱼ ≤ 1`, `xₖₗ⟨aₖₗ⟩ > Σᵢ Σⱼ xᵢⱼ(1 - xᵢₗ)\|aᵢₗ\|` for all `k, l`, `xᵢⱼ ∈ {0, 1}`: a picked component satisfies (12) and gives a strictly dominant sub-matrix. | [`SubmatrixLpCounterexample.lean`](../../src/CORALean/Global/SubmatrixLpCounterexample.lean) — `subLp13_infeasible`; the corrected constraint is (14), `det_submatrix_ne_zero_of_lp14` **Counterexample:** `subLp16_counterexample` | `fixed` — at any `xₖₗ = 0` the constraint reads `0 > (a sum ≥ 0)`, so (13) is infeasible once `m ≥ 2`; read as (14), the implication `xₖₗ = 1 ⇒ …`, it is sound |
| `Eq. 14` | `xₖₗ = 1 ⇒ ⟨aₖₗ⟩ > Σ_{i≠k} Σⱼ xᵢⱼ \|aᵢₗ\|`. | [`SubmatrixLp.lean`](../../src/CORALean/Global/SubmatrixLp.lean) — `det_submatrix_ne_zero_of_lp14`: every real matrix in `A` is regular on the picked sub-matrix (column dominance) | `correct` |
| `Eq. 15` | (Big-M) `Σ_{i≠k} Σⱼ xᵢⱼ \|aᵢₗ\| ≤ M + (⟨aₖₗ⟩ - μ - M) xₖₗ`, `M` large enough to deactivate it at `xₖₗ = 0`, `μ` small. | [`SubmatrixLp.lean`](../../src/CORALean/Global/SubmatrixLp.lean) — `det_submatrix_ne_zero_of_lp15`, for `μ > 0` and any `M` | `correct` |
| `Eq. 16` | (13) with (15): `max Σ xᵢⱼ` s.t. the row and column constraints and `Σ_{i≠k} Σⱼ xᵢⱼ \|aᵢₗ\| ≤ M + (⟨aₖₗ⟩ + μ - M) xₖₗ`; solved by an LP solver, it extracts a strictly dominant interval matrix. | [`SubmatrixLpCounterexample.lean`](../../src/CORALean/Global/SubmatrixLpCounterexample.lean) — `subLp16_counterexample`; with `-μ` as in (15), `det_submatrix_ne_zero_of_lp15` **Counterexample:** `subLp16_counterexample` | `fixed` — `+μ` allows a column sum of `⟨aₖₗ⟩ + μ`: the all-ones `2 × 2` matrix at `x = I` is feasible and singular; the sign of (15) repairs it |
| `Def. 4.7` | (Comparison matrix) `⟨A⟩ᵢᵢ = ⟨Aᵢᵢ⟩`, `⟨A⟩ᵢⱼ = -\|Aᵢⱼ\|`, `i ≠ j`. | [`HMatrix.lean`](../../src/CORALean/Global/HMatrix.lean) — inside `IsHMatrix`, and `compMat_mulVec_apply` | `correct` |
| `Def. 4.8` | (H-matrix) `A` is an H-matrix iff `⟨A⟩u > 0` for some `u > 0`. | [`HMatrix.lean`](../../src/CORALean/Global/HMatrix.lean) — `IsHMatrix` | `correct` |
| `Thm. 4.9` | Every H-matrix is regular. | n/a — restated from Neumaier 1990 [19]; proved as `det_ne_zero_of_isHMatrix`, which (17) uses | `restated` |
| `Remark 4.1` | A strictly diagonally dominant interval matrix is an H-matrix, at `u = 1`. | [`HMatrixRegular.lean`](../../src/CORALean/Global/HMatrixRegular.lean) — `isHMatrix_of_dominant` | `correct` |
| `Eq. 17` | `Σ_{i≠k} Σⱼ xᵢⱼ \|aᵢₗ\| uᵢⱼ ≤ M + (⟨aₖₗ⟩uₖₗ - μ - M) xₖₗ`, `uᵢⱼ > 0`: the picks give an H-sub-matrix. | [`SubmatrixLp.lean`](../../src/CORALean/Global/SubmatrixLp.lean) — `det_submatrix_ne_zero_of_lp17`: the transpose of the picked sub-matrix is an H-matrix, so it is regular; `μ > 0`, `u > 0` at the picks | `correct` |
| `Eq. 18` | (17) at `uᵢⱼ = ⟨aᵢⱼ⟩⁻¹`, `⟨aₖₗ⟩⟨aₖₗ⟩⁻¹ = 1`, solvable by linear programming. | [`SubmatrixLp.lean`](../../src/CORALean/Global/SubmatrixLp.lean) — `det_submatrix_ne_zero_of_lp18`, with `Remark 4.2` as a hypothesis | `correct` |
| `Remark 4.2` | `⟨aₖₗ⟩` must differ from `0` because of the division in (18). | n/a — the hypothesis `h42` of `det_submatrix_ne_zero_of_lp18` | `not-a-claim` |
| `Thm. 4.10` | (Rohn [22, Cor. 5.1]) `A = mid(A) + [-Δ, Δ]`, `D = \|mid(A)⁻¹\|Δ`: `ρ(D) < 1` gives `A` regular. | n/a — restated from Rohn 1989 [22] | `restated` |
| `Alg. 4` | (Extraction of a regular interval sub-matrix) For `k` from `min(n, m)` down, try `MAX_ITERATION` random diagonals and return the first sub-matrix `Thm. 4.10` finds regular. | n/a — a randomized search, a subject CORALean does not cover; that what it returns is regular is `Thm. 4.10`'s test | `not-covered` |
| `Sec. 4.3.4` | Experiments on sub-matrix extraction: computing times (Figs. 5-6) and estimated ranks (Figs. 7-8); the combinatorial method finds larger regular sub-matrices than the dominance LP. | n/a — experiments | `not-a-claim` |
| `Sec. 5` | Inner approximations of an immersion `ℝ² → ℝ³` (19) and a submersion `ℝ³ → ℝ²` (20) (Figs. 9-12). | n/a — experiments | `not-a-claim` |

## Findings

**`Cor. 3.1` — the step to (i).** The proof shows that (5) implies condition (i) of `Thm. 3.1`,
`y₁ ∩ f₁:ᵣ(∂u) = ∅`: if `y₁ = f₁:ᵣ(u)` for some `u ∈ ∂u`, the mean-value theorem puts `u₁` in
`H`, "and `u₁ ∈ ∂u₁` which contradicts (5)". But `∂u` for `u = u₁ × u₂` also holds the points
with `u₁` interior and `u₂` at a bound, where nothing is contradicted. For `f(x₁, x₂) = x₁` on
`[-1, 1]²`, `ũ = 0`, the point intervals `J₁ = 1`, `J₂ = 0` and `y₁ = [-1/2, 1/2]`, (5) reads
`y₁ ⊆ (-1, 1)` and holds, while `(0, 1) ∈ ∂u` is mapped to `0 ∈ y₁`
(`innerTest_step_counterexample`). The corollary is still true: on the slice
`v ↦ f₁:ᵣ(v, ũ₂)`, a submersion by (3), every point of `∂u₁` that reaches `y₁` lies in `H`,
since the `J₂` term vanishes there, and `Thm. 3.1` applies to the slice on `u₁`
(`Icc_subset_image_of_innerTest`). The `J₂(u₂ - ũ₂)` term only makes (5) harder to satisfy.
[`InnerRangeTest.lean`](../../src/CORALean/Global/InnerRangeTest.lean)

**`Eq. 13` and `Eq. 16`.** (13) is (14) without the gate on `xₖₗ`: for every pair with `xₖₗ = 0`
it demands `0 > Σᵢ Σⱼ xᵢⱼ(1 - xᵢₗ)|aᵢₗ| ≥ 0`, and a row with two or more columns has such a
pair (`subLp13_infeasible`). (16) flips the sign of `μ` from (15), so at `xₖₗ = 1` it allows
`Σ_{i≠k} Σⱼ xᵢⱼ|aᵢₗ| = ⟨aₖₗ⟩ + μ ≥ ⟨aₖₗ⟩`: for the all-ones `2 × 2` matrix, `x = I`,
`μ = 1/100` and the paper's `M = Σ aᵢⱼ = 4`, every constraint holds and the picked
matrix is singular (`subLp16_counterexample`). (14), (15), (17) and (18) are sound
(`det_submatrix_ne_zero_of_lp14` to `_lp18`); none of them needs `M`.
[`SubmatrixLpCounterexample.lean`](../../src/CORALean/Global/SubmatrixLpCounterexample.lean)

Not formalized as a whole, so recorded without a class: `Alg. 3` returns true on `ũ + t ⊆ ũ`,
a closed inclusion, where `Cor. 3.1` needs `int(u₁)`; CORA's `aux_InnerGeneral` does the same.
The closed version is true: on the slice at `ũ₂` the test is the Jacobi step of the square
case, whose map `x ↦ x̃ + Diag⁻¹A(x)(b - OffDiag A(x)(x - x̃))` with the average Jacobian `A(x)`
is a continuous self-map of the box, and Brouwer's theorem fixes a zero
(`exists_mem_Icc_eq_add_of_jacobi`, `Icc_subset_image_of_innerTest_closed`). CORA's
`aux_InnerGeneral` subtracts `J₂(u₂ - ũ₂)` after the division by the diagonal rather than
before; that interval contains `0`, so the test it computes still contains the slice's and
stays sound. `Alg. 3` as printed also overwrites `x̃` by its midpoint (line 3), repeats line 7
as line 8 and subtracts `ũ₁ - ũ₁` (line 14).
