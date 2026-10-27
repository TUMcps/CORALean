# Distributed Set-Based Observers Using Diffusion Strategies

```bibtex
@article{alanwar2003distributed,
  author = {Alanwar, A. and Rath, J. J. and Said, H. and Johansson, K. H. and Althoff, M.},
  title = {Distributed Set-Based Observers Using Diffusion Strategies},
  journal = {Journal of the Franklin Institute},
  year = {2023}
}
```

**Source:** https://arxiv.org/pdf/2003.10347v3 (arXiv v3, 18 Jun 2023, the accepted manuscript, 11 pages, read in full; text extracted with `pypdf`). The typeset article was not reachable. The arXiv versions are titled "Strategy" (v1) and "Strategies" (v3, the published title); CORA cites it as "Distributed Set-Based Observers Using Diffusion Strategy" in `@zonotope/private/priv_andAveraging.m` and `@zonotope/intersectStrip.m`, without a result number. Numbering is v3's.  
**Inventory:** confirmed (against v3: Definitions 1-4, Lemma 1, Theorems 1-2, Propositions 1-2 and Algorithms 1-2, each with its own counter; the equations below are the numbered displays that make a claim)

Two distributed set-based observers on a network of nodes, each estimating the state of a linear
discrete-time system by a zonotope: a strip-based one (`Alg. 1`) and a set-propagation one
(`Alg. 2`). Both are followed by a diffusion step in which a node intersects its zonotope with its
neighbours' by one lightweight formula (`Thm. 1`), a weighted average of centers and a
concatenation of weighted generators. CORA's `and(Z1, Z2, 'averaging')` is that formula
(`priv_andAveraging`, `Zonotope.andAveraging`), with the closed-form weights of `Prop. 1`. The
formula, both weight and gain optimality statements and the Luenberger step are formalized over
ℝ, and the loops `Alg. 1` and `Alg. 2` are assembled from them, with the enclosure of the true
state proved at every instant.

## Results

| Result | What it says | In CORALean | Class |
|---|---|---|---|
| `Def. 1` | (Zonotope) Z = ⟨c, G⟩ = {c + Σᵢ β⁽ⁱ⁾g⁽ⁱ⁾ \| -1 ≤ β⁽ⁱ⁾ ≤ 1}. | n/a — restated; tracked as `Def. 1` on [Girard 2005](../2005/girard-hscc-reachability-zonotopes.md) | `restated` |
| `Eq. 2` | The Minkowski sum is Z₁ ⊕ Z₂ = ⟨c₁ + c₂, [G₁, G₂]⟩, computed exactly. | n/a — restated from Kühn 1998 [42]; `Zonotope.plus_exact` | `restated` |
| `Eq. 3` | The linear map is L Z₁ = ⟨L c₁, L G₁⟩, computed exactly. | n/a — restated from Kühn 1998 [42]; `Zonotope.mtimes_exact` | `restated` |
| `Eq. 4` | tr(cA) = c tr(A). | n/a — Mathlib's `Matrix.trace_smul` | `mathlib` |
| `Eq. 5` | tr(A + B) = tr(A) + tr(B). | n/a — Mathlib's `Matrix.trace_add` | `mathlib` |
| `Eq. 6` | ∇ₓ tr(A X B Xᵀ C) = Aᵀ Cᵀ X B ᵀ + C A X B. | n/a — restated from the Matrix Cookbook [44, p. 11] | `restated` |
| `Eq. 7` | ∇ₓ tr(Bᵀ Xᵀ C X B) = Cᵀ X B Bᵀ + C X B Bᵀ. | n/a — restated from the Matrix Cookbook [44, p. 11] | `restated` |
| `Def. 2` | (Predicted state set) Ẑₖ = F Ẑₖ₋₁ ⊕ Z_{Q,k} (Eq. 9). | n/a — a definition, of the strip-based observer's time update | `not-a-claim` |
| `Def. 3` | (Measurement state set) The states consistent with yᵢₖ and vᵢₖ ∈ ⟨0, diag(rᵢₖ)⟩: the strip {x \| \|Hᵢx - yᵢₖ\| ≤ rᵢₖ} for p = 1, the intersection of strips for p > 1 (Eq. 10). | n/a — a definition | `not-a-claim` |
| `Def. 4` | (Corrected state set) A zonotope Z̄ₖ with Ẑₖ ∩ Sₖ ⊆ Z̄ₖ (Eq. 11). | n/a — a definition, of the contract the measurement update has | `not-a-claim` |
| `Lemma 1` | (From Le et al. [40]) The intersection of the zonotope ⟨ĉ, Ĝ⟩ with the strips of the measurements is over-approximated by ⟨c̄, Ḡ⟩, c̄ = ĉ + Λ(ȳ - Γĉ), Ḡ = [(I - ΛΓ)Ĝ, ΛR], for every design matrix Λ (Eq. 12). | n/a — restated from [40]; tracked as `Prop. 6` on [Le et al. 2013](../2013/le-automatica-zonotopic-estimation.md) | `restated` |
| `Alg. 1` | (Distributed strip-based diffusion observer) Step 1, the measurement update with the gain Λ of minimal ‖Ḡ‖_F; Step 2, the diffusion update: weights w of minimal ‖Ǵ‖_F, center and generators as in `Thm. 1`, order reduction ↓q; Step 3, the time update ĉ = Fć, Ĝ = [F G̃, Q]. | [`DiffusionStrip.lean`](../../src/CORALean/ContSet/Zonotope/Real/Operations/DiffusionStrip.lean), [`DiffusionStripStep.lean`](../../src/CORALean/ContSet/Zonotope/Real/Operations/DiffusionStripStep.lean), [`DiffusionStripMeasurement.lean`](../../src/CORALean/ContSet/Zonotope/Real/Operations/DiffusionStripMeasurement.lean), [`DiffusionUpdate.lean`](../../src/CORALean/ContSet/Zonotope/Real/Operations/DiffusionUpdate.lean), [`DiffusionTimeUpdate.lean`](../../src/CORALean/ContSet/Zonotope/Real/Operations/DiffusionTimeUpdate.lean), [`DiffusionStripOuter.lean`](../../src/CORALean/ContSet/Zonotope/Real/Theorems/DiffusionStripOuter.lean) — `Zonotope.diffusionStrip` runs the instants from `Z₀`, each `diffusionStripStep` one named `let` per step: Step 1 at every node, `Λ` of `stripGain` (Eq. 38) into `intersectStrip` (Eqs. 12-13); Step 2, `diffusionUpdate` over the neighbours `N_i`, the weights of `averagingWeights` (Eq. 19), `andAveraging` (Eqs. 14-15) and `reduce` for `↓q`; Step 3, `diffusionTimeUpdate`. `diffusionStrip_outer`: a state sequence `x_{k+1} = F x_k + Q_k β_k` from `Z₀` whose outputs meet every node's strips is in every node's set at every instant, given `tr(Ḡʲ Ḡʲᵀ) > 0` of Prop. 1 | `underspecified` — Step 2's weights are an `argmin` of `‖Ǵ‖_F` only up to a common factor (`Ǵ` is homogeneous of degree 0 in `𝔴`) and the closed form of Prop. 1 needs `tr(Ḡʲ Ḡʲᵀ) > 0`, which the algorithm does not state. `↓q` is any enclosing reduction and `Ẑ_{s,k} = Z₀` leaves open which instant it is the prediction of; supplied; see Findings |
| `Thm. 1` | The intersection of the zonotopes Z̄ʲ = ⟨c̄ʲ, Ḡʲ⟩, j ∈ Nᵢ, is over-approximated by ⟨ć, Ǵ⟩, ć = (Σⱼ wʲ c̄ʲ) / Σⱼ wʲ (Eq. 14), Ǵ = [w¹Ḡ¹, …, wᵐḠᵐ] / Σⱼ wʲ (Eq. 15), for weights with Σⱼ wʲ ≠ 0. | [`AndAveraging.lean`](../../src/CORALean/ContSet/Zonotope/Real/Operations/AndAveraging.lean), [`AndAveragingOuter.lean`](../../src/CORALean/ContSet/Zonotope/Real/Theorems/AndAveragingOuter.lean) — any real weights of nonzero sum, negative entries included | `correct` |
| `Prop. 1` | For ⟨ć, Ǵ⟩ of `Thm. 1`, the weights of sum one minimizing ‖Ǵ‖_F (Eq. 18) are wʲ = 1 / (tr(Ḡʲ Ḡʲᵀ) Σᵣ 1 / tr(Ḡʳ Ḡʳᵀ)) (Eq. 19). | [`AveragingWeights.lean`](../../src/CORALean/ContSet/Zonotope/Real/Operations/AveragingWeights.lean), [`AveragingWeightsOptimal.lean`](../../src/CORALean/ContSet/Zonotope/Real/Theorems/AveragingWeightsOptimal.lean) — these weights have sum one and the least ‖Ǵ‖²_F among weights of sum one, by completing the square in place of a bordered Hessian | `underspecified` — tr(Ḡʲ Ḡʲᵀ) > 0 is missing: a zero generator matrix leaves 1 / tr undefined; supplied |
| `Thm. 2` | For x̂ₖ₋₁ ∈ ⟨ĉ, Ĝ⟩, nₖ ∈ ⟨0, Q⟩ and v̄ₖ ∈ ⟨0, R⟩, the observer xₖ = F xₖ₋₁ + nₖ + Λ(ȳ - Γxₖ₋₁ - v̄) (Eq. 27) lies in ⟨c̄, Ḡ⟩, c̄ = Fĉ + Λ(ȳ - Γĉ) (Eq. 28), Ḡ = [(F - ΛΓ)Ĝ, -ΛR, Q] (Eq. 29). | [`LuenbergerUpdate.lean`](../../src/CORALean/ContSet/Zonotope/Real/Operations/LuenbergerUpdate.lean), [`LuenbergerUpdateOuter.lean`](../../src/CORALean/ContSet/Zonotope/Real/Theorems/LuenbergerUpdateOuter.lean) — any gain Λ and measurement ȳ | `correct` |
| `Alg. 2` | (Distributed set-propagation diffusion observer) Step 1, the Luenberger update with the gain Λ of minimal ‖Ḡ‖_F; Step 2, the diffusion update as in `Alg. 1`, order reduction ↓q. | [`DiffusionProp.lean`](../../src/CORALean/ContSet/Zonotope/Real/Operations/DiffusionProp.lean), [`DiffusionPropStep.lean`](../../src/CORALean/ContSet/Zonotope/Real/Operations/DiffusionPropStep.lean), [`DiffusionPropLuenberger.lean`](../../src/CORALean/ContSet/Zonotope/Real/Operations/DiffusionPropLuenberger.lean), [`DiffusionUpdate.lean`](../../src/CORALean/ContSet/Zonotope/Real/Operations/DiffusionUpdate.lean), [`DiffusionPropOuter.lean`](../../src/CORALean/ContSet/Zonotope/Real/Theorems/DiffusionPropOuter.lean) — `Zonotope.diffusionProp` runs the instants from `Z₀`, each `diffusionPropStep` one named `let` per step: Step 1 at every node, `Λ` of `luenbergerGain` (Eq. 31) into `luenbergerUpdate` (Eqs. 28-29); Step 2, `diffusionUpdate` as in `Alg. 1`. `diffusionProp_outer`: a state sequence `x_k = F x_{k-1} + Q_k β_k` from `Z₀` is in every node's set at every instant when the output fed at instant `k` meets the node's strips at `x_{k-1}`, given `tr(Ḡʲ Ḡʲᵀ) > 0` | `underspecified` — the same weights and `↓q` as `Alg. 1`. And the innovation `ȳ_k - Γ x̂_{k-1}` of Eq. 27 pairs the output of instant `k` with the state of instant `k - 1`, so the sets hold the true state of Eq. 8 only for the output of the previous instant; supplied; see Findings |
| `Prop. 2` | The gain Λ minimizing ‖Ḡ‖_F of `Thm. 2` (Eq. 30) is Λ = F Ĝ Ĝᵀ Γᵀ (Γ Ĝ Ĝᵀ Γᵀ + R Rᵀ)⁻¹ (Eq. 31). | [`LuenbergerGain.lean`](../../src/CORALean/ContSet/Zonotope/Real/Operations/LuenbergerGain.lean), [`LuenbergerGainOptimal.lean`](../../src/CORALean/ContSet/Zonotope/Real/Theorems/LuenbergerGainOptimal.lean) — the squared Frobenius norm at any other gain is the one at Λ plus ‖(Λ' - Λ)ΓĜ‖²_F + ‖(Λ' - Λ)R‖²_F, which is what the vanishing gradient (Eq. 33-34) amounts to | `underspecified` — the invertibility of Γ Ĝ Ĝᵀ Γᵀ + R Rᵀ, which the formula writes as a quotient, is missing; supplied |
| `Eq. 35` | Λᵥ = F Λₛ: the set-propagation gain is the strip-based gain multiplied by F. | [`LuenbergerGainEqMulStripGain.lean`](../../src/CORALean/ContSet/Zonotope/Real/Theorems/LuenbergerGainEqMulStripGain.lean) — the closed forms of Eq. 31 and Eq. 38, each the minimizer (`Prop. 2`, `Eq. 38`) | `correct` |
| `Sec. 5` | The diffusion Kalman filter's incremental update (Eq. 36-37) and diffusion update, and the analogy P ≡ ḠḠᵀ, R ≡ RRᵀ, x ≡ c̄ (Eq. 39) with the observer's; for equal initial centers, covariances and weights, and no reduction error, the two observers have the same gain and center. | n/a — an analogy with the stochastic filter, argued in prose | `not-a-claim` |
| `Eq. 38` | The strip-based gain is Λₛ = Ĝ Ĝᵀ Γᵀ (Γ Ĝ Ĝᵀ Γᵀ + R Rᵀ)⁻¹, the minimizer of ‖Ḡ‖_F of Lemma 1 with Λ = Λₛ. | [`StripGain.lean`](../../src/CORALean/ContSet/Zonotope/Real/Operations/StripGain.lean), [`StripGainOptimal.lean`](../../src/CORALean/ContSet/Zonotope/Real/Theorems/StripGainOptimal.lean) — minimal among the generators of `Zonotope.intersectStrip` at the strips \|Γx - y\| ≤ φ, R = diag φ, as `Prop. 2` at F = I with no process noise | `underspecified` — the same invertibility as `Prop. 2` is missing; supplied |
| `Sec. 6` | A localization example of eight nodes tracking a rotating object: both observers against the diffusion Kalman filter and Garcia et al. on Hausdorff distance and estimate size, with and without diffusion and measurement sharing (Figs. 2-4, Tables 1-3). | n/a — experiments | `not-a-claim` |

## Findings

**`Prop. 1`, `Prop. 2`, `Eq. 38` — a denominator that may vanish.** The weights are written
1 / tr(Ḡʲ Ḡʲᵀ), the gains with a quotient by Γ Ĝ Ĝᵀ Γᵀ + R Rᵀ. A zero generator matrix has
trace zero, and the measurement noise R = diag(r) of a strip with r = 0 makes R Rᵀ singular
wherever ΓĜ is rank-deficient; the statements hold with the positive trace and the invertible
matrix assumed, which is what the formalization takes.
[`AveragingWeightsOptimal.lean`](../../src/CORALean/ContSet/Zonotope/Real/Theorems/AveragingWeightsOptimal.lean),
[`LuenbergerGainOptimal.lean`](../../src/CORALean/ContSet/Zonotope/Real/Theorems/LuenbergerGainOptimal.lean)

**`Alg. 1`, `Alg. 2` — what Step 2 and the first instant leave open.** Step 2 reads
`𝔴 = argmin ‖Ǵ‖_F`, and `Ǵ = [𝔴¹Ḡ¹, …]/Σ 𝔴` does not change when `𝔴` is scaled, so the minimizer is
a ray; the text before Prop. 1 fixes `Σ 𝔴 = 1`, and Prop. 1's closed form needs
`tr(Ḡʲ Ḡʲᵀ) > 0` (see above), which the algorithms do not state. The enclosure theorems take that
positivity as a hypothesis. `↓q` is a free enclosing reduction (CORA's `reduce` to an order here),
and `Ẑ_{s,k} = Z₀` for the first instant does not say which instant it predicts: the loop starts
at the prediction the first measurement update uses.

**`Alg. 2` — which output goes with which state.** Eq. 27 reads `x_k = F x_{k-1} + n_k +
Λ(ȳ_k - Γ x_{k-1} - v̄_k)`, so Thm. 2 and Step 1 pair the output of instant `k` with the state of
instant `k - 1`, and what Thm. 2 bounds is the state of that observer, not of the system of Eq. 8.
The system's state `x_k = F x_{k-1} + n_k` is a state of the observer when the innovation
`ȳ_k - Γ x_{k-1} - v̄_k` is zero for an admissible `v̄_k`, which the output `Γ x_{k-1} + v̄_k` of
instant `k - 1` gives and the output `H x_k + v_k` of instant `k` does not. That is what
`diffusionProp_outer` assumes; the paper states no enclosure of the system's state for `Alg. 2` and
evaluates it numerically (Figs. 3-4, a slowly rotating `F`). The process noise has the same slip:
Eq. 8 drives `x_k` to `x_{k+1}` with `n_k`, Eq. 27 drives `x_{k-1}` to `x_k` with it;
`diffusionStrip` follows Eq. 8, `diffusionProp` Eq. 27.
