# Bounded error identification of systems with time-varying parameters

```bibtex
@article{bravo2006bounded,
  author = {Bravo, J. M. and Alamo, T. and Camacho, E. F.},
  title = {Bounded error identification of systems with time-varying parameters},
  journal = {IEEE Transactions on Automatic Control},
  year = {2006}
}
```

**Source:** https://idus.us.es/handle/11441/94329 (the University of Sevilla repository record of the article, doi:10.1109/TAC.2006.878750). Its attached file, `CDC 04_ThC12.3_Bravo.pdf`, is not the article: it is the authors' six-page conference paper of the same title (43rd IEEE Conference on Decision and Control, Bahamas, 2004, paper ThC12.3, pages from 4063; read in full, text extracted with `pypdf`), whose abstract differs from the record's ("This note presents …"). The IEEE article was not reachable, so **the rows below are the conference version's results under its own numbering, not the journal note's**.  
**Inventory:** unconfirmed (the conference version prints Assumptions 1-2, Definitions 1-9, Property 1 and Theorem 1, each with its own counter, and the algorithm of Sec. 3.3 without a number; the seven-page note may add results and renumber)

Set-membership identification of the parameters of a linear regression `y_k = r_kᵀθ_k + e_k`,
`|e_k| ≤ σ`, that vary by at most `γ` per step: the exact feasible set is an intersection of strips
swollen by the expansion, and its outer approximation is a zonotope that each measurement
intersects with a strip (the bound of [Alamo et al. 2005](../2005/alamo-automatica-guaranteed-estimation.md)),
whose gain is chosen to minimize the volume and which is then widened by the box of the expansion
(`Sec. 3.3`). CORA's `intersectStrip` has the method `'bravo'`, which applies `Property 1` along
each generator in turn and keeps the zonotope of smallest approximate volume. The method of that
name is not in the conference version, and so has no row. What the tree has of the paper is the
guarantee of the algorithm: the feasible set of `Def. 1`, its recursion, the tight strip and the
enclosure of one step; the volume formula it uses is proved on the page of Alamo et al. Two
readings the paper leaves open, and the two senses of `FSS_k`, are under Findings.

## Results

| Result | What it says | In CORALean | Class |
|---|---|---|---|
| `Assumption 1` | Measurements `y_1, …, y_N` with `y_k = r_kᵀθ_k + e_k`, the regression vector `r_k`, the parameters `θ_k` and the error `e_k ∈ E = {e ∈ ℝ : \|e\| ≤ σ}`. | n/a — the paper's setting | `not-a-claim` |
| `Assumption 2` | The parameters are time-varying with a bounded expansion, `‖θ_k - θ_{k-1}‖_∞ ≤ γ` for all `k`, the scalar `γ > 0` the expansion factor. | n/a — the paper's setting (the example takes `γ` a vector, one bound per parameter) | `not-a-claim` |
| `Def. 1` | (Feasible Solution Set) For the pairs `(y_k, r_k)`, `k = 1, …, N`: `θ` is in the FSS if there are `θ_1, …, θ_N` with (i) `θ = θ_N`, (ii) `\|y_k - r_kᵀθ_k\| ≤ σ`, `k = 1, …, N`, (iii) `‖θ_k - θ_{k-1}‖_∞ ≤ γ`, `k = 2, …, N`. | [`FeasibleSolutionSet.lean`](../../src/CORALean/Global/FeasibleSolutionSet.lean) — `feasibleSolutionSet`, the runs `θ_1, …, θ_N` by an explicit sequence; `γ` a vector of per-parameter bounds (a scalar is the constant vector) and an initial set `Θ₀` for `θ_1`, which the paper's example uses (`Θ₀ = univ` is the definition as printed) | `correct` |
| `Def. 2` | (Approximated Feasible Solution Set) An AFSS is a set that fulfils `FSS ⊆ AFSS`. | n/a — a name for an outer bound; the enclosures are `Sec. 3.3` | `not-a-claim` |
| `Def. 3` | (Minkowski sum) `X ⊕ Y = {x + y : x ∈ X, y ∈ Y}`. | n/a — restated; tracked as `Def. 10` on [Alamo et al. 2005](../2005/alamo-automatica-guaranteed-estimation.md) | `restated` |
| `Def. 4` | (Unitary interval) `B = [-1, 1]`. | n/a — restated; tracked as `Def. 5` on [Alamo et al. 2005](../2005/alamo-automatica-guaranteed-estimation.md) | `restated` |
| `Def. 5` | (Unitary box) `Bᵐ` is a vector of `m` unitary intervals. | n/a — restated; tracked as `Def. 7` on [Alamo et al. 2005](../2005/alamo-automatica-guaranteed-estimation.md) | `restated` |
| `Def. 6` | (Zonotope of order `m`) For `p ∈ ℝⁿ` and `H ∈ ℝⁿˣᵐ`, the set `p ⊕ H Bᵐ` is a zonotope of order `m`: the Minkowski sum of the segments defined by the columns of `H`. | n/a — the zonotope of Girard, restated; tracked as `Def. 1` on [Girard 2005](../2005/girard-hscc-reachability-zonotopes.md) | `restated` |
| `Sec. 3` | The feasible set for time-varying parameters is obtained by the recursion `FSS_{k+1} = (FSS_k ∩ F_{d_k}) ⊕ γ Bⁿ`, `F_{d_k} = {θ : -σ ≤ r_kᵀθ - y_k ≤ σ}` the strip of the measurement `d_k = (y_k, r_k)`; for time-invariant parameters `FSS_{k+1} = FSS_k ∩ F_{d_k}`. | [`PredictedSolutionSet.lean`](../../src/CORALean/Global/PredictedSolutionSet.lean), [`FeasibleSolutionSetEqPredicted.lean`](../../src/CORALean/Global/FeasibleSolutionSetEqPredicted.lean) — the recursion as `predictedSolutionSet` (the printed `FSS_{k+1}` is `predictedSolutionSet … k`), and `feasibleSolutionSet_eq_predicted`: `Def. 1`'s set after `N + 1` measurements is `predictedSolutionSet … N` met with the last strip | `underspecified` — `FSS_k` names `Def. 1`'s set (which has met the strip of measurement `k`) and, in the recursion, the set before measurement `k`; with the recursion's reading the identity with `Def. 1` is an equation to prove, done here |
| `Sec. 3 (expansion)` | If `AFSS_k ∩ F_{d_k}` is approximated by the zonotope `p ⊕ H Bᵐ`, `FSS_{k+1} ⊆ p ⊕ H Bᵐ ⊕ γ Bⁿ = p ⊕ [H  γ I] Bᵐ⁺ⁿ`. | n/a — restated; tracked as `Sec. 2` on [Girard 2005](../2005/girard-hscc-reachability-zonotopes.md) | `restated` |
| `Property 1` | For the zonotope `X = p ⊕ H Bʳ ⊂ ℝⁿ`, the strip `S = {x : \|cᵀx - d\| ≤ σ}` and the vector `λ`, with `p̂(λ) = p + λ(d - cᵀp)` and `Ĥ(λ) = [(I - λcᵀ)H  σλ]`, `X ∩ S ⊆ X̂(λ) = p̂(λ) ⊕ Ĥ(λ) Bʳ⁺¹`. | n/a — restated; tracked as `Property 2` on [Alamo et al. 2005](../2005/alamo-automatica-guaranteed-estimation.md) | `restated` |
| `Sec. 3.1` | (Minimizing the volume of the intersection) The volume of a zonotope is a sum of `2ⁿ \|det\|` of selections of `n` columns, and `Vol(p̂(λ) ⊕ Ĥ(λ) Bʳ⁺¹)` is a convex function of `λ`: finding the `λ` that minimizes it is a convex problem. | n/a — restated; tracked as `Sec. 6.1 (convexity)` on [Alamo et al. 2005](../2005/alamo-automatica-guaranteed-estimation.md) | `restated` |
| `Thm. 1` | The volume of `X̂(λ)` of `Property 1` is `Σ_{i=1}^{N(n,r)} 2ⁿ \|1 - cᵀλ\| \|det(A_i)\| + Σ_{i=1}^{N(n-1,r)} σ 2ⁿ \|det[B_i v_i]\| \|v_iᵀλ\|`, `A_i` the matrices of `n` and `B_i` those of `n - 1` columns of `H`, `v_i` orthonormal to `Imag(B_i)`; the proof is that of the authors' earlier paper, included for completeness. | n/a — restated; tracked as `Sec. 6.1` on [Alamo et al. 2005](../2005/alamo-automatica-guaranteed-estimation.md) | `restated` |
| `Def. 7` | (Support hyperplanes) `S_1 = {x : cᵀx = r}` and `S_2 = {x : cᵀx = q}` are tangent to `Z = p ⊕ H Bᵐ` if `r = max_{x∈Z} cᵀx` and `q = min_{x∈Z} cᵀx`, which are `r = cᵀp + ‖Hᵀc‖₁` and `q = cᵀp - ‖Hᵀc‖₁`. | [`SupportRadius.lean`](../../src/CORALean/ContSet/Zonotope/Real/Operations/SupportRadius.lean), [`SupportDotProduct.lean`](../../src/CORALean/ContSet/Zonotope/Real/Theorems/SupportDotProduct.lean) — `support_dotProduct`: `IsGreatest` and `IsLeast` of the image of `Z` under `cᵀ·`, so the values are attained | `correct` |
| `Def. 8` | (Support strip) For `Z = p ⊕ H Bᵐ` and `c`, `F_S = {x : q ≤ cᵀx ≤ r}` with `q`, `r` of the support hyperplanes. | [`SupportStrip.lean`](../../src/CORALean/ContSet/Zonotope/Real/Operations/SupportStrip.lean) — `Zonotope.supportStrip`, with `q`, `r` the values of `Def. 7` | `correct` |
| `Def. 9` | (Tight strip) For `Z = p ⊕ H Bᵐ` and a strip `F = {x : q_0 ≤ cᵀx ≤ r_0}`, `F_T = F_S ∩ F`, `F_S` the support strip of `c` and `Z`. | n/a — the intersection of two sets; its use is `Sec. 3.2` | `not-a-claim` |
| `Sec. 3.2` | "With these definitions: `F ∩ Z = F_S ∩ F ∩ Z = F_T ∩ Z`": intersecting the zonotope with the tight strip loses nothing, and `F_T ⊆ F` gives a better result. | [`ConstructInterSupportStripInterEq.lean`](../../src/CORALean/ContSet/Zonotope/Real/Theorems/ConstructInterSupportStripInterEq.lean) — for every set `F`, which a strip is; `F_T ⊆ F` is `F_S ∩ F ⊆ F` | `correct` |
| `Sec. 3.3` | The identification algorithm: with `AFSS_k = X = p ⊕ H Bʳ`, (1) build the strip `F_{d_k} = {θ : -σ ≤ r_kᵀθ - y_k ≤ σ}`, (2) build the tight strip `F_{T_k}`, (3) build the parametric zonotope `X̂(λ) = p̂(λ) ⊕ Ĥ(λ) Bʳ⁺¹`, (4) compute `λ*` minimizing its size, (5) `AFSS_{k+1} = X̂(λ*) ⊕ γ I Bⁿ = p̂(λ*) ⊕ [Ĥ(λ*)  Iγ] Bʳ⁺¹⁺ⁿ`. | [`IdentifyStep.lean`](../../src/CORALean/ContSet/Zonotope/Real/Operations/IdentifyStep.lean), [`IdentifyStepOuter.lean`](../../src/CORALean/ContSet/Zonotope/Real/Theorems/IdentifyStepOuter.lean) — steps 2, 3 and 5 for any gain `λ` (step 4 chooses it, the enclosure does not depend on it); the guarantee is that `AFSS_{k+1}` contains `(P ∩ F_{d_k}) ⊕ γ Bⁿ` for every set `P` the zonotope contains, which is the recursion of `Sec. 3` | `underspecified` — step 3 applies `Property 1` to a strip `\\|cᵀx - d\\| ≤ σ`, while step 2 gives the tight strip as `q ≤ cᵀx ≤ r`; the center `(q + r)/2` and half-width `(r - q)/2` are supplied, and the convention that `γ` is a vector (the example) not a scalar (`Assumption 2`) |
| `Sec. 4` | An example: a linear system with time-varying parameters `y_k = 0.9 y_{k-1} - 0.8 y_{k-2} - u_k - 0.8 u_{k-1} + w_k + e_k`, 100 measurements, zonotopes of at most forty segments, compared with the parallelotope method. | n/a — an experiment | `not-a-claim` |

## Findings

**The rows are the conference version's.** The journal note (IEEE TAC 51(7), 2006) could not be obtained; the repository record holds the 2004 conference paper under the note's title. The inventory is that paper's, marked unconfirmed, and a row's label may differ in the note.

**`FSS_k` is two sets.** `Def. 1` defines the feasible solution set after `N` measurements, `θ = θ_N`, which has met the strip of measurement `N`. The recursion `FSS_{k+1} = (FSS_k ∩ F_{d_k}) ⊕ γ Bⁿ` of `Sec. 3` intersects `FSS_k` with the strip of measurement `k` once more, so there `FSS_k` is the set before measurement `k`, and the recursion does not compute `Def. 1`'s set but the one before the next measurement; `Def. 1`'s set after `N` measurements is that set met with the last strip, which is proved (`feasibleSolutionSet_eq_predicted`). The algorithm of `Sec. 3.3` follows the second reading, as its `AFSS_k ∩ F_{d_k}` shows.

**The tight strip is not converted to the form `Property 1` takes.** `Property 1` bounds the intersection of a zonotope and a strip `{x : |cᵀx - d| ≤ σ}`; `Def. 9` gives the tight strip `F_T = F_S ∩ F` as an interval `{x : q ≤ cᵀx ≤ r}`, and step 3 of the algorithm applies `Property 1` to it. The conversion, center `(q + r)/2` and half-width `(r - q)/2` (with an empty tight strip when `q > r`, which `Property 1` then covers vacuously), is written out in `Zonotope.identifyStep`.

**One bound on the parameter change, or one per parameter.** `Assumption 2` takes a scalar `γ`, and `Sec. 3` writes `θ_{k+1} = θ_k ⊕ γ Bⁿ` and `[H  γ I]`; the example in `Sec. 4` takes `γ = (0.01, 0.01, 0.01, 0.01, 0.05)`, one bound per parameter, and the expansion `[Ĥ(λ*)  Iγ]` with a vector `γ` has to read `diag(γ)`. The formalization takes the vector, a scalar being the constant vector.

**Not a finding but a disclosure on the volume.** `Thm. 1` states the volume of the zonotope that bounds the intersection; it is proved on the page of Alamo et al. as an identity for `Zonotope.volume`, the quoted sum of `2ⁿ |det|`, not for the Lebesgue measure beyond zonotopes with `n` generators.
