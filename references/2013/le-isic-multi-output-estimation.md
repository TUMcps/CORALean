# Zonotope-based set-membership estimation for multi-output uncertain systems

```bibtex
@inproceedings{le2013zonotope,
  author = {Le, V. T. H. and Stoica, C. and Alamo, T. and Camacho, E. F. and Dumur, D.},
  title = {Zonotope-based set-membership estimation for multi-output uncertain systems},
  booktitle = {2013 IEEE International Symposium on Intelligent Control (ISIC)},
  year = {2013}
}
```

**Source:** the published paper (2013 IEEE ISIC, part of the IEEE Multi-Conference on Systems and Control, Hyderabad, August 28-30, 2013, pp. 212-217, doi:10.1109/ISIC.2013.6658619, 6 pages), provided by the user and read in full; text extracted with PyMuPDF.  
**Inventory:** confirmed (Properties 1-6, Definitions 1-2, Algorithm 1 and Proposition 1, each with its own counter, the example after `Prop. 1`, and Equations 1-18; Eqs. 2-7 are the proof of `Prop. 1`; Sec. V is the example with Table I)

The multi-output step of CORA's `PRad-B` and of `@zonotope/intersectStrip`'s numeric `Λ`: the
predicted zonotope is met with the polytope that the strips of all outputs cut out at once, and
the intersection is enclosed by one zonotope in a gain matrix `Λ` (`Prop. 1`), against the strips
one after the other of [Le et al. 2013](le-automatica-zonotopic-estimation.md). The enclosure and
the observer step built on it are formalized at every `Λ`. The offline choice of `Λ = P⁻¹ Y` by the
matrix inequality on the P-radius (Eqs. 11-17) is not; that inequality has a misprinted block and
the interval-matrix prediction of Sec. IV a claim with no argument (under Findings).

## Results

| Result | What it says | In CORALean | Class |
|---|---|---|---|
| `Sec. II` | Notation: intervals with `mid` and `rad`, `B = [-1, 1]`, boxes, interval matrices and `vert([M])`, the row-sum diagonal matrix `rs(M)`, strips `{x : \|cᵀx - y\| ≤ φ}`, zonotopes `p ⊕ H Bᵐ`, and the P-radius `L = max_{z ∈ Z} ‖z - p‖²_P` for `P = Pᵀ ≻ 0`. | n/a — restated from Le et al. (IFAC 2011); tracked as `Sec. 2` on [Le et al. 2013](le-automatica-zonotopic-estimation.md), which prints the same notation and P-radius | `restated` |
| `Property 1` | (After Combastel 2003) `Z₁ ⊕ Z₂ = (c₁ + c₂) ⊕ [H₁ H₂] Bᵐ¹⁺ᵐ²`. | n/a — restated; tracked as `Sec. 2` on [Girard 2005](../2005/girard-hscc-reachability-zonotopes.md) | `restated` |
| `Property 2` | (After Combastel 2003) `K · Z₁ = K c₁ ⊕ (K H₁) Bᵐ¹`. | n/a — restated; tracked as `Sec. 2` on [Girard 2005](../2005/girard-hscc-reachability-zonotopes.md) | `restated` |
| `Property 3` | (Zonotope reduction, after Combastel 2003 and Alamo et al. 2005) Sorting the columns of `H` by decreasing Euclidean norm, keeping the first `s - n` and replacing the rest `Ĥ_n` by `rs(Ĥ_n)` gives `Z ⊆ p ⊕ [Ĥ_{s-n} rs(Ĥ_n)] Bˢ`. | n/a — restated; tracked as `Sec. 3.2` on [Combastel 2003](../2003/combastel-ecc-state-bounding-observer.md) | `restated` |
| `Property 4` | (Zonotope inclusion, after Alamo et al. 2005) `p ⊕ [M] Bᵐ ⊆ ♦(Z) = p ⊕ [mid([M]) rs(rad([M]))] Bᵐ⁺ⁿ`. | n/a — restated; tracked as `Thm. 4` on [Alamo et al. 2005](../2005/alamo-automatica-guaranteed-estimation.md) | `restated` |
| `Property 5` | `mid([M] N) = mid([M]) N` and `rad([M] N) = rad([M]) \|N\|`. | n/a — restated; tracked as `Prop. 5` on [Le et al. 2013](le-automatica-zonotopic-estimation.md), the same authors' statement of it | `restated` |
| `Property 6` | An interval vector is the zonotope `[c] = mid([c]) ⊕ rs(rad([c])) Bⁿ`. | n/a — the box as a zonotope, restated | `restated` |
| `Eq. 1` | The system `x_{k+1} = A x_k + ω_k`, `y_k = C x_k + v_k`, `A` constant and unknown in a quadratically stable interval matrix `[A]`, `(C, A)` detectable, `ω_k ∈ W = F Bⁿˣ`, `v_k ∈ V = Φ Bⁿʸ`, `F`, `Φ` diagonal, `x₀ ∈ X₀`. | n/a — the paper's setting | `not-a-claim` |
| `Def. 1` | (After Alamo et al. 2005) The consistent state set `X_{y_k} = {x : y_k - C x ∈ V}`, the polytope `{x : \|C x - y_k\| ≤ [φ₁ … φ_{n_y}]ᵀ}` of `n_y` strips. | n/a — restated; tracked as `Def. 1` on [Le et al. 2013](le-automatica-zonotopic-estimation.md) | `restated` |
| `Def. 2` | (After Alamo et al. 2005) The exact uncertain set `X_k = (A X_{k-1} ⊕ W) ∩ X_{y_k}`, `k ≥ 1`, is the set of states consistent with the measurements and `X₀`. | n/a — restated; tracked as `Def. 2` on [Le et al. 2013](le-automatica-zonotopic-estimation.md) | `restated` |
| `Alg. 1` | 1) Prediction `X̄_k = A X̂_{k-1} ⊕ W`; 2) the consistent set `X_{y_k}` from `y_k`; 3) correction: an outer approximation `X̂_k` of `X_{y_k} ∩ X̄_k`. | [`ObserveStep.lean`](../../src/CORALean/ContDynamics/LinearSysDT/Operations/ObserveStep.lean), [`ObserveStepOuter.lean`](../../src/CORALean/ContDynamics/LinearSysDT/Theorems/ObserveStepOuter.lean) — `LinearSysDT.observeStep` with the strips met all at once by `intersectStrip`, and `observeStep_outer`: the result holds every `A x + ω`, `x ∈ X̂_{k-1}`, `ω ∈ W`, in the strips, at every gain | `correct` |
| `Prop. 1` | For any `Λ ∈ ℝ^{n×m}`, a zonotope `Z = p ⊕ H Bʳ` and the polytope `P_o = {x : \|C x - d\| ≤ [φ₁ … φ_m]ᵀ}`, `φᵢ ≥ 0`: with `p̂(Λ) = p + Λ (d - C p)`, `Ĥ(Λ) = [(I - Λ C) H  Λ Φ]`, `Φ = diag(φ₁, …, φ_m)`, `Z ∩ P_o ⊆ Ẑ(Λ) = p̂(Λ) ⊕ Ĥ(Λ) Bʳ⁺ᵐ`. | [`IntersectStrip.lean`](../../src/CORALean/ContSet/Zonotope/Real/Operations/IntersectStrip.lean), [`IntersectStripOuter.lean`](../../src/CORALean/ContSet/Zonotope/Real/Theorems/IntersectStripOuter.lean) — `Zonotope.intersectStrip_outer`, for every `Λ` and every `φ` | `correct` |
| `Eq. 2` | `x = p + H s₁`, `s₁ ∈ Bʳ`. | n/a — a step of the proof of `Prop. 1` | `not-a-claim` |
| `Eq. 3` | `x = p + Λ C H s₁ + (I - Λ C) H s₁`. | n/a — a step of the proof of `Prop. 1` | `not-a-claim` |
| `Eq. 4` | `x ∈ P_o`, so `C x - d = Φ s₂` for some `s₂ ∈ Bᵐ`. | n/a — a step of the proof of `Prop. 1` | `not-a-claim` |
| `Eq. 5` | `x = p + Λ (d - C p) + Λ Φ s₂ + (I - Λ C) H s₁`. | n/a — a step of the proof of `Prop. 1` | `not-a-claim` |
| `Eq. 6` | `x = p̂(Λ) + Ĥ(Λ) [s₁; s₂]`. | n/a — a step of the proof of `Prop. 1` | `not-a-claim` |
| `Eq. 7` | `x ∈ p̂(Λ) ⊕ Ĥ(Λ) Bʳ⁺ᵐ = Ẑ(Λ)`. | n/a — the conclusion of the proof of `Prop. 1` | `not-a-claim` |
| `Example` | `Prop. 1` on a zonotope in `ℝ²` with three generators and three strips, `Λ` chosen by segment minimization (Fig. 1). | n/a — an illustration | `not-a-claim` |
| `Eq. 8` | The prediction `X̄_k = A p̂_{k-1} ⊕ [A Ĥ_{k-1}  F] Bʳ⁺ⁿʷ`. | n/a — `Property 1` and `Property 2` at the prediction; tracked as `Sec. 2` on [Girard 2005](../2005/girard-hscc-reachability-zonotopes.md) | `restated` |
| `Eq. 9` | `X_{y_k} = {x : \|C x - y_k\| ≤ [φ₁ … φ_{n_y}]ᵀ}`. | n/a — `Def. 1` written out | `not-a-claim` |
| `Eq. 10` | `Prop. 1` at the prediction: `X̂_k(Λ) = p̂_k(Λ) ⊕ Ĥ_k(Λ) Bʳ⁺ⁿˣ⁺ⁿʸ`, `p̂_k(Λ) = A p̂_{k-1} + Λ (y_k - C A p̂_{k-1})`, `Ĥ_k(Λ) = [(I - Λ C) A Ĥ_{k-1}  (I - Λ C) F  Λ Φ]`, which contains `X̄_k ∩ X_{y_k}`. | [`IntersectStripOuter.lean`](../../src/CORALean/ContSet/Zonotope/Real/Theorems/IntersectStripOuter.lean) — `Zonotope.intersectStrip_outer` at the zonotope `A p̂_{k-1} ⊕ [A Ĥ_{k-1} F] B` of `Eq. 8`, whose generators met with `[(I - Λ C) ·, Λ Φ]` are those of `Ĥ_k(Λ)` | `correct` |
| `Eq. 11` | The design condition on the P-radius, `L_k ≤ β L_{k-1} + max_{s ∈ Bⁿˣ} ‖F s‖²₂ + φ₁² + … + φ²_{n_y}`, `β ∈ (0, 1]`, a relaxation of `L_k ≤ β L_{k-1}`. | n/a — the condition the gain is chosen to meet; that the gain of `Eq. 17` meets it is `Eq. 12` to `Eq. 16` | `not-a-claim` |
| `Eq. 12` | `Eq. 11` in the equivalent form `max_ẑ ‖Ĥ_k ẑ‖²_P ≤ max_z β ‖Ĥ_{k-1} z‖²_P + max_s ‖F s‖²₂ + φ₁² + … + φ²_{n_y}`, `ẑ = (z, s, η₁, …, η_{n_y})`, the maxima over the unit boxes. | — | — |
| `Eq. 13` | A sufficient condition for `Eq. 12`: `max_ẑ (‖Ĥ_k ẑ‖²_P - β ‖Ĥ_{k-1} z‖²_P - ‖F s‖²₂ - φ₁² - … - φ²_{n_y}) ≤ 0`. | — | — |
| `Eq. 14` | Adding `Σᵢ φᵢ² (1 - ηᵢ²) ≥ 0` gives a sufficient condition for `Eq. 13`: `ẑᵀ Ĥ_kᵀ P Ĥ_k ẑ - β zᵀ Ĥ_{k-1}ᵀ P Ĥ_{k-1} z - sᵀ Fᵀ F s - Σᵢ φᵢ² ηᵢ² ≤ 0` for all `ẑ`. | — | — |
| `Eq. 15` | `Eq. 14` with `Σᵢ φᵢ² ηᵢ² = ηᵀ Φᵀ Φ η`. | — | — |
| `Eq. 16` | The matrix inequality `[βP 0 0 AᵀP - AᵀCᵀYᵀ; ∗ FᵀF 0 FᵀP - FᵀCᵀYᵀ; ∗ ∗ ΦᵀΦ YᵀΦ; ∗ ∗ ∗ P] ≽ 0` in `β ∈ (0, 1]`, `P` and `Y = P Λ`, a sufficient condition for `Eq. 15`; affine in `A`, so it holds on `[A]` when it holds at the vertices. | — | — |
| `Eq. 17` | `max τ` over `τ, β, P, Y` subject to `(1 - β) P / ε ≽ τ I`, `Eq. 16` at every vertex `Sᵢ` of `[A]`, and `τ > 0`, with `ε = max_s ‖F s‖²₂ + φ₁² + … + φ²_{n_y}`: the smallest ellipsoid `{x : xᵀ (1 - β) P x / ε ≤ 1}` around the limit P-radius `L_∞ = ε/(1 - β)`; `Λ = P⁻¹ Y`. | — | — |
| `Sec. IV (interval prediction)` | For `A ∈ [A]`, `[A] p̂_k ⊕ [[A] Ĥ_k  F] B` lies in `mid([A]) p̂_k ⊕ G Bˡ`, `G = [mid([A]) Ĥ_k  F  rs(rad([A]) \|Ĥ_k\|)  rs(rad([A]) \|p̂_k\|)]`, `l = r + 2n + n_ω`, by `Property 4` to `Property 6`; and "the non-increasing property of the estimation set is preserved". | — | — |
| `Sec. V` | The example (Eq. 18): a two-state, two-output system with an interval parameter, the gain of `Eq. 17` by PENBMI, the estimates against the svd-based method of Combastel 2003 (Figs. 2-3) and run times (Table I). | n/a — an experiment | `not-a-claim` |

## Findings

**`Eq. 16` misprints a block.** The `(3, 4)` block of the matrix inequality is printed `Yᵀ Φ`. With
`Y = P Λ ∈ ℝ^{n_x×n_y}` and `Φ ∈ ℝ^{n_y×n_y}`, that product is defined only when `n_x = n_y`. The
inequality is the Schur complement of `diag(βP, FᵀF, ΦᵀΦ) - Mᵀ P M ≽ 0`, `M = [(I - Λ C) A  (I -
Λ C) F  Λ Φ]`, whose last block column is `Mᵀ P`; its third block is `(Λ Φ)ᵀ P = Φᵀ Yᵀ = Φ Yᵀ`,
as the first two, `AᵀP - AᵀCᵀYᵀ` and `FᵀP - FᵀCᵀYᵀ`, already have it. In the paper's example
`n_x = n_y = 2` and `Φ = 0.2 I`, so `Yᵀ Φ = Φ Yᵀ` and the reported design is not affected. The
same block appears in `Eq. 17`. CORA's `priv_observe_gain_PRadB` makes the same correction.

**The interval prediction of Sec. IV comes with no argument for the P-radius.** The enclosure of
`[A] p̂_k ⊕ [[A] Ĥ_k F] B` by `mid([A]) p̂_k ⊕ G Bˡ` follows from `Property 4` to `Property 6`.
The closing claim, that "the non-increasing property of the estimation set is preserved" because
`rad([A]) |p̂_k|` stays bounded, does not follow from `Eq. 12` to `Eq. 16`: those bound
`Ĥ_k = [(I - Λ C) A Ĥ_{k-1}  (I - Λ C) F  Λ Φ]` for one `A`, and say nothing of the generators
`rs(rad([A]) |Ĥ_k|)` and `rs(rad([A]) |p̂_k|)` that the enclosure adds.

**The limit of the P-radius after `Eq. 16`.** "At infinity, the expression (11) is equivalent to
`L_∞ = β L_∞ + ε`", giving `L_∞ = ε/(1 - β)` for `β ∈ (0, 1]`. `Eq. 11` is an inequality, the
limit need not exist, and at `β = 1` the quotient is undefined. For `β < 1` the recursion gives
`L_k ≤ βᵏ L_0 + ε/(1 - β)` directly, an upper bound on `limsup L_k`; the same remark is under
Findings on [Le et al. 2013](le-automatica-zonotopic-estimation.md).
