# Set-membership approach and Kalman observer based on zonotopes for discrete-time descriptor systems

Y. Wang, V. Puig and G. Cembrano. "Set-membership approach and Kalman observer based on zonotopes for discrete-time descriptor systems". Automatica, 93:435-443, 2018.

**Source:** https://upcommons.upc.edu/bitstream/2117/120598/1/2036-Set-membership-approach-and-Kalman-observer-based-on-zonotopes-for-discrete-time-descriptor-systems.pdf (the accepted manuscript on UPCommons, "Preprint submitted to Automatica Accepted 7 March 2018", 17 pages, read in full; text extracted with `pypdf`). The typeset article (doi:10.1016/j.automatica.2018.03.082) was not reachable.  
**Inventory:** confirmed (against the manuscript: Definitions 1-5, Theorems 1-7, Propositions 1-2 and Remarks 1-2, each with its own counter; Equations 1-40, of which the rows below are the displays outside a theorem that make a claim, the others being parts of the theorems they belong to; Sec. 6 is the example)

The estimator behind CORA's `FRad-B` (`'wang-FRad'`), `PRad-C` and `Nom-G`, for the descriptor
system `E x₊ = A x + B u + D ω + D_d d`, `y = C x + F υ` with an unknown input `d` decoupled by
`TE + NC = I`, `TD_d = 0`: the intersection zonotope at a correction matrix `Λ` (Thm. 1), the
Kalman gain that minimizes its F_W-radius (Thm. 2), the LMI that makes its W-radius contract
(Thm. 3, Prop. 1), the online bound (Thm. 4), the prediction-type zonotopic Kalman observer
and its optimal gain (Thms. 5, 6), the stability of the nominal observer (Prop. 2) and the
equivalence of the two approaches (Thm. 7). The gain optimality is proved by completing the
square rather than by the paper's matrix derivatives. `Thm. 4`'s bound is false as printed and
proved in corrected form; `Prop. 1`'s proof assumes a limit exists; several dimensions are
misprinted. CORA's `'wang-FRad'` gain applies the dynamics twice (FINDINGS).

## Results

| Result | What it says | In CORALean | Class |
|---|---|---|---|
| `Eq. 1` | A zonotope `⟨p, H⟩ = {p + H z, z ∈ Bᵐ}`. | n/a — restated; tracked as `Def. 1` on [Girard 2005](../2005/girard-hscc-reachability-zonotopes.md) | `restated` |
| `Eq. 2` | `⟨p₁, H₁⟩ ⊕ ⟨p₂, H₂⟩ = ⟨p₁ + p₂, [H₁ H₂]⟩` (2a), `L ⊙ ⟨p, H⟩ = ⟨Lp, LH⟩` (2b), `⟨p, H⟩ ⊆ ⟨p, rs(H)⟩` (2c). | n/a — restated; tracked as `Sec. 2` on [Girard 2005](../2005/girard-hscc-reachability-zonotopes.md) (2a, 2b), the interval hull (2c) as `Sec. 3.4` there | `restated` |
| `Eq. 3` | The matrix derivatives `∂/∂X tr(A Xᵀ B) = AᵀBᵀ` (3a) and `∂/∂X tr(A X B Xᵀ C) = BXᵀCA + BᵀXᵀAᵀCᵀ` (3b). | n/a — matrix calculus, which CORALean does not formalize; `Thm. 2` and `Thm. 6` are proved by completing the square instead | `not-covered` |
| `Eq. 4` | The descriptor system `E x₊ = A x + B u + D ω + D_d d`, `y = C x + F υ`, `E` possibly singular, `x₀ ∈ ⟨p₀, H₀⟩`, `ω`, `υ` in unit boxes, `d` unknown and unbounded. | n/a — the paper's setting | `not-a-claim` |
| `Eq. 6` | The rank condition Eq. 5 (the unknown input can be decoupled) gives matrices `T`, `N` with `TE + NC = I` (6a) and `TD_d = 0` (6b). | — | — |
| `Def. 1` | The uncertain state set `X̄ = {x \| E x ∈ A X̄₋ ⊕ B u₋ ⊕ D_d d ⊕ D W}`. | [`DescriptorPredictSet.lean`](../../src/CORALean/ContDynamics/LinearSysDT/Definitions/DescriptorPredictSet.lean) — over every `d` | `underspecified` — the unknown input `d` is free in the printed set; read as some `d` |
| `Def. 2` | The measurement state set `P = {x \| \|C x - y\| ≤ F}`. | [`MeasurementSet.lean`](../../src/CORALean/ContDynamics/LinearSysDT/Definitions/MeasurementSet.lean) — `C x - y ∈ F Bⁿᵛ` | `underspecified` — `\|C x - y\| ≤ F` compares a vector with a matrix; read as `C x - y ∈ ⟨0, F⟩`, what the proof of `Thm. 1` uses |
| `Def. 3` | The exact uncertain state set `X = X̄ ∩ P`. | [`IntersectDescriptorOuter.lean`](../../src/CORALean/ContDynamics/LinearSysDT/Theorems/Real/IntersectDescriptorOuter.lean) — the left side of its inclusion | `correct` |
| `Thm. 1` | (Intersection zonotope) With `TE + NC = I`, `TD_d = 0` and `x ∈ ⟨p̂, H̄⟩`, every `x₊ ∈ X̂₊ ∩ P₊` lies in `⟨p̂₊(Λ), Ĥ₊(Λ)⟩`, `p̂₊ = (I - ΛC)TA p̂ + (I - ΛC)TB u + (N + Λ - ΛCN) y₊`, `Ĥ₊ = [(I - ΛC)TA H̄  (I - ΛC)TD  (I - ΛC)NF  ΛF]` (Eq. 7), for every `Λ`. | [`IntersectDescriptor.lean`](../../src/CORALean/ContSet/Zonotope/Real/Operations/IntersectDescriptor.lean), [`IntersectDescriptorOuter.lean`](../../src/CORALean/ContDynamics/LinearSysDT/Theorems/Real/IntersectDescriptorOuter.lean) | `correct` |
| `Def. 4` | The F_W-radius `ℓ_{F,W} = ‖⟨p, H⟩‖_{F,W} = ‖H‖_{F,W} = √tr(HᵀWH)`, `W = Wᵀ ≻ 0`. | [`FWRadius.lean`](../../src/CORALean/ContSet/Zonotope/Real/Definitions/FWRadius.lean) | `correct` |
| `Def. 5` | The W-radius `ℓ_W = max_{z ∈ Z} ‖z - p‖²_{2,W} = max_{b ∈ Bʳ} ‖H b‖²_{2,W}`. | [`PRadius.lean`](../../src/CORALean/ContSet/Zonotope/Real/Definitions/PRadius.lean) — Le et al.'s P-radius, the same quantity | `correct` |
| `Eq. 11` | `ℓ_{F,W+} = ‖Ĥ₊(Λ)‖²_{F,W} = tr(Ĥ₊ᵀ W Ĥ₊) = tr(W Ĥ₊Ĥ₊ᵀ) = tr(W P₊(Λ))`. | [`FWRadiusSqEqTrace.lean`](../../src/CORALean/ContSet/Zonotope/Real/Theorems/FWRadiusSqEqTrace.lean) — for the square, at any zonotope | `underspecified` — `Def. 4` names the norm `ℓ_{F,W}`, Eq. 11 its square; formalized for the square, which has the same minimizer |
| `Thm. 2` | (Kalman correction matrix) `Λ* = L S⁻¹`, `L = R̄Cᵀ`, `S = C R̄ Cᵀ + Q_v`, `R̄ = T(A P̄ Aᵀ + Q_w)Tᵀ + N Q_v Nᵀ`, `P̄ = H̄H̄ᵀ`, minimizes the F_W-radius of `⟨p̂₊(Λ), Ĥ₊(Λ)⟩`; it does not depend on `W`. | [`IntersectDescriptorFWRadiusLe.lean`](../../src/CORALean/ContSet/Zonotope/Real/Theorems/IntersectDescriptorFWRadiusLe.lean) — for every `W` with `vᵀWv ≥ 0`, `S` invertible as `S⁻¹` presupposes | `correct` |
| `Eq. 16` | The W-radius of the intersection zonotope, `ℓ_{W+} = max_{z ∈ B^{q+n_x+2n_y}} ‖Ĥ₊(Λ) z‖²_{2,W} = zᵀĤ₊ᵀWĤ₊z`. | [`IntersectDescriptorPRadiusLe.lean`](../../src/CORALean/ContSet/Zonotope/Real/Theorems/IntersectDescriptorPRadiusLe.lean) — `Def. 5` at the zonotope of `Thm. 1` | `underspecified` — the box is `B^{q+n_w+2n_v}`, the generator count of Eq. 7b, and the last expression drops the maximum |
| `Thm. 3` | (W-radius criterion) With `γ ∈ (0, 1)`, `ε > 0`: if `W ≻ 0`, `Y`, diagonal `Γ ∈ ℝ^{n_x×n_x}`, `Υ, Ω ∈ ℝ^{n_y×n_y}` satisfy the LMI Eq. 18, `Γ, Υ, Ω ≻ 0` (Eq. 19) and `tr Γ + tr Υ + tr Ω < ε` (Eq. 20), then `ℓ_{W+} ≤ γ ℓ_W + ε` (Eq. 17) at `Λ = W⁻¹Y`. | [`IntersectDescriptorPRadiusLe.lean`](../../src/CORALean/ContSet/Zonotope/Real/Theorems/IntersectDescriptorPRadiusLe.lean) — `Γ` sized `n_w`, `Υ, Ω` sized `n_v`; any bound `ℓ` of `ℓ_W`, any `γ ≥ 0` | `underspecified` — `Γ`, `Υ`, `Ω` multiply the coefficients of `D` and `F`, so they are `n_w × n_w` and `n_v × n_v`; the printed `n_x`, `n_y` (and `W ∈ ℝ^{n_x}`) fit only when `n_w = n_x`, `n_v = n_y`, as in the example; see Findings |
| `Prop. 1` | (Ultimate bound) If Eq. 17 holds with `γ ∈ (0, 1)`, `ε > 0`, the W-radius is ultimately bounded, `ℓ_{W,∞} ≤ ε/(1 - γ)` (Eq. 25). | [`UltimateBoundOfRecurrence.lean`](../../src/CORALean/Global/UltimateBoundOfRecurrence.lean) — `ℓ_k ≤ γᵏ ℓ_0 + ε/(1 - γ)`, and eventually below `ε/(1 - γ) + δ` for every `δ > 0` | `proof-gap` — the proof takes `k → ∞` in Eq. 17 as if `ℓ_k` converged; it need not, and the bound holds for the limit superior without it; see Findings |
| `Eq. 26` | The offline gain `Λ_f = W⁻¹Y` from `min -tr(W)` subject to Eq. 18-20, to shrink the ultimate bound. | n/a — the choice among feasible gains; every one is covered by `Thm. 3` | `not-a-claim` |
| `Thm. 4` | (Online bound) If the matrix `W` of Eq. 26 and a diagonal `M ∈ ℝ^{n_x×n_x}` satisfy `[M ⋆; WĤ₊ W] ≻ 0` (Eq. 27), then `ℓ_{W+} < max_{z ∈ B} ‖M z‖²₂` (Eq. 28). | [`PRadiusLtOfLmi.lean`](../../src/CORALean/ContSet/Zonotope/Real/Theorems/PRadiusLtOfLmi.lean), [`PRadiusLtOfLmiCounterexample.lean`](../../src/CORALean/ContSet/Zonotope/Real/Theorems/PRadiusLtOfLmiCounterexample.lean) — the corrected bound `ℓ_{W+} < max_z zᵀMz = tr M`, `M` sized by the generator count, at least one generator; and the counterexample to Eq. 28 **Counterexample:** `Zonotope.pRadius_lt_of_lmi_counterexample` | `fixed` — `⟨0, [1/2]⟩`, `W = 1`, `M = 1/2` satisfy Eq. 27 with `ℓ_{W+} = 1/4 = max (z/2)²`; the proof shows `zᵀĤᵀWĤz < zᵀMz`, i.e. the bound `tr M` that Eq. 29 minimizes; see Findings |
| `Eq. 29` | The online gain `Λ_o` from `min tr(M)` subject to Eq. 27. | n/a — the choice among feasible gains | `not-a-claim` |
| `Remark 1` | The offline gain may already suffice; the online update need not improve much. | n/a — a remark | `not-a-claim` |
| `Thm. 5` | (Prediction-type zonotopic observer) With `TE + NC = I`, `TD_d = 0` and `x ∈ ⟨p̂, H̄⟩`, `x₊ ∈ ⟨p̂₊(G), Ĥ₊(G)⟩`, `p̂₊ = (TA - GC)p̂ + TBu + Gy + Ny₊`, `Ĥ₊ = [(TA - GC)H̄  TD  -NF  -GF]` (Eq. 31), for the observer structure Eq. 30. | [`ObserveDescriptor.lean`](../../src/CORALean/ContSet/Zonotope/Real/Operations/ObserveDescriptor.lean), [`ObserveDescriptorOuter.lean`](../../src/CORALean/ContDynamics/LinearSysDT/Theorems/Real/ObserveDescriptorOuter.lean) — for every gain `G` | `correct` |
| `Thm. 6` | (Optimal Kalman observer gain) `G* = TA K`, `K = L̃S̃⁻¹`, `L̃ = P̃Cᵀ`, `S̃ = C P̃ Cᵀ + Q_v`, `P̃ = H̄H̄ᵀ`, minimizes the F_W-radius of `⟨0, Ĥ₊(G)⟩`; it does not depend on `W`. | [`ObserveDescriptorFWRadiusLe.lean`](../../src/CORALean/ContSet/Zonotope/Real/Theorems/ObserveDescriptorFWRadiusLe.lean) — for every `W` with `vᵀWv ≥ 0`, `S̃` invertible | `correct` |
| `Prop. 2` | The nominal Luenberger observer `x̂₊ = TA x̂ + TBu + Ḡ(y - Cx̂) + Ny₊` is μ-stable if `[μW ⋆; WTA - YC  W] ≻ 0` (Eq. 36), `Y = WḠ`. | [`DescriptorObserverDecay.lean`](../../src/CORALean/ContDynamics/LinearSysDT/Theorems/Real/DescriptorObserverDecay.lean) — `eᵀ₊We₊ < μ eᵀWe` for every error `e ≠ 0` | `correct` |
| `Thm. 7` | The set-membership approach is equivalent to the current-estimation-type zonotopic observer Eq. 37: its zonotope Eq. 39 is that of Eq. 7 at `Λ = Ĝ`, the signs of the last two generator blocks not mattering. | [`ObserveDescriptorCurrent.lean`](../../src/CORALean/ContSet/Zonotope/Real/Operations/ObserveDescriptorCurrent.lean), [`ObserveDescriptorCurrentEq.lean`](../../src/CORALean/ContSet/Zonotope/Real/Theorems/ObserveDescriptorCurrentEq.lean) — the two zonotopes are the same set | `correct` |
| `Remark 2` | So `Ĝ` can be chosen by the methods of Sec. 3. | n/a — a remark, by `Thm. 7` | `not-a-claim` |
| `Eq. 40` | (Sec. 5.2) For `rank E = n_x`, `T̄ + N̄C = I`, `T̄D_d = 0` give `D_d = N̄CD_d`, `T̄ = I - N̄C`, and, `D_d` of full column rank, such `T̄`, `N̄` exist iff `rank D_d = rank CD_d`. | — | — |
| `Sec. 6` | A three-state descriptor example: bounds, MSE and run times of the gains `Λ*`, `Λ_f`, `Λ_o`, `G*`, `Ḡ`, `Ĝ` (Figs. 1-4, Tables 1-2). | n/a — an experiment | `not-a-claim` |

## Findings

**`Thm. 4` — the printed bound is false; the proof's bound is right.** Eq. 28 reads
`ℓ_{W+} < max_{z ∈ B} ‖M z‖²₂`, which for a diagonal `M` is `Σ mᵢ²`. The proof shows
`zᵀĤ₊ᵀWĤ₊z < zᵀMz` for all `z` (from `M - Ĥ₊ᵀWĤ₊ ≻ 0`, the Schur complement of Eq. 27), and
`max_z zᵀMz = Σ mᵢ = tr M` is what Eq. 29 then minimizes. In one dimension `⟨0, [1/2]⟩`, `W = 1`,
`M = 1/2` satisfy Eq. 27 (`[1/2 1/2; 1/2 1] ≻ 0`), and `ℓ_{W+} = 1/4 = max_{|z|≤1} (z/2)²`, so the
strict inequality fails
([`PRadiusLtOfLmiCounterexample.lean`](../../src/CORALean/ContSet/Zonotope/Real/Theorems/PRadiusLtOfLmiCounterexample.lean));
`ℓ_{W+} < tr M` holds
([`PRadiusLtOfLmi.lean`](../../src/CORALean/ContSet/Zonotope/Real/Theorems/PRadiusLtOfLmi.lean)).
`M` is also printed `n_x × n_x`; it multiplies the coefficient vector, so it is
`(q + n_w + 2n_v) × (q + n_w + 2n_v)`.

**`Prop. 1` — the limit is assumed.** "We take `k → ∞` in (17) to obtain
`ℓ_{W,∞} ≤ γ ℓ_{W,∞} + ε`" presumes `ℓ_k` converges. Unrolling Eq. 17 gives
`ℓ_k ≤ γᵏ ℓ_0 + ε/(1 - γ)`, so every `δ > 0` has `ℓ_k ≤ ε/(1 - γ) + δ` eventually, which is the
ultimate bound with no limit taken.

**Dimensions in `Thm. 3` and Eq. 16.** `Γ` weighs `b₁ ∈ Bⁿʷ`, the coefficients of `D`, and `Υ`,
`Ω` weigh `b₂, b₃ ∈ Bⁿᵛ`, those of `NF` and `F`; the theorem prints them `n_x × n_x` and
`n_y × n_y`, the proof's Eq. 24 boxes `B^{n_x}`, `B^{n_y}`, and Eq. 16 the box `B^{q+n_x+2n_y}`,
while Eq. 7b has `q + n_w + 2n_v` generators. All agree in the example (`n_w = n_x = 3`,
`n_v = n_y = 2`). The formalization sizes them by what they multiply.
