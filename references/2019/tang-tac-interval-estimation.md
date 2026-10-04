# Interval estimation methods for discrete-time linear time-invariant systems

W. Tang, Z. Wang, Y. Wang, T. Raïssi and Y. Shen. "Interval estimation methods for discrete-time linear time-invariant systems". IEEE Transactions on Automatic Control, 64(11):4717-4724, 2019.

**Source:** https://hal.science/hal-02467321/document (the accepted manuscript on HAL, "Tang2017tacDraft.pdf", 12 pages after HAL's cover page, read in full; text extracted with `pypdf`, pages 5-6 also read as rendered images for the bars and signs of Eqs. 27-43). The typeset article (doi:10.1109/TAC.2019.2902673) was not reachable.  
**Inventory:** confirmed (against the manuscript: Definitions 1-3, Properties 1-4, Lemmas 1-5, Theorems 1-8, Proposition 1, Remarks 1-4 and Algorithm 1, each with its own counter; Equations 1-81, of which the rows below are the displays outside a theorem, proposition or lemma, the others being parts of the results they belong to; Sec. VII is the example)

The interval estimator behind CORA's `Hinf-G` (`priv_observe_gain_HinfG`, `priv_observe_interval`):
a Luenberger observer whose gain is designed by an `H∞` linear matrix inequality (Thm. 1), and
the box of its reachable error added to the estimate (Thm. 2, Alg. 1), which encloses the
state at every gain and, as Sec. VI shows, is never wider than the zonotope method or either
interval observer at the same gain (Thms. 6-8), its box being the interval hull of the
reachable error. All of it is formalized; the `H∞` bound is stated as a bound on the transfer
matrix on the unit circle, without a transfer-function library. The boundedness bound of
Thm. 3 is false as printed (strict) and proved with `≤`; Lemma 5's `A I = [A a, A b]` is false
and its hull version true; Remark 2's reduction omits absolute values; Thms. 7 and 8 omit the
hypothesis that makes the compared observer one. Alg. 1 seeds the error set correctly with
`⟨0, H₀⟩`, where CORA's `priv_observe_interval` seeds it with the initial set itself
(FINDINGS.md).

## Results

| Result | What it says | In CORALean | Class |
|---|---|---|---|
| `Def. 1` | An interval vector (box) `I = [a, b] = {x \| aᵢ ≤ xᵢ ≤ bᵢ}`; `Bᵐ = [-1, 1]ᵐ`. | n/a — restated; tracked as `Sec. 2` on [Althoff and Grebenyuk 2017](../2017/althoff-arch-interval-arithmetic.md), whose intervals are the same boxes (`Interval`) | `restated` |
| `Property 1` | `[a, b] ⊕ [c, d] = [a + c, b + d]`. | n/a — restated; tracked as `Eq. 2` on [Althoff and Grebenyuk 2017](../2017/althoff-arch-interval-arithmetic.md) | `restated` |
| `Def. 2` | The interval hull `Box(S)`, the smallest interval vector containing `S`. | [`Hull.lean`](../../src/CORALean/ContSet/Interval/Real/Definitions/Hull.lean), [`HullIsLeast.lean`](../../src/CORALean/ContSet/Interval/Real/Theorems/HullIsLeast.lean) — coordinatewise `sInf`/`sSup`, the smallest box for a nonempty bounded `S` | `correct` |
| `Property 2` | `Box(S₁ ⊕ … ⊕ Sₘ) = Box(S₁) ⊕ … ⊕ Box(Sₘ)` (Eq. 3). | [`HullAdd.lean`](../../src/CORALean/ContSet/Interval/Real/Theorems/HullAdd.lean) — for two nonempty bounded sets, the `m`-fold sum following by induction | `correct` |
| `Def. 3` | An `m`-order zonotope `⟨p, H⟩ = {p + H z : z ∈ Bᵐ}`. | n/a — restated; tracked as `Def. 1` on [Girard 2005](../2005/girard-hscc-reachability-zonotopes.md) | `restated` |
| `Property 3` | `⟨p₁, H₁⟩ ⊕ ⟨p₂, H₂⟩ = ⟨p₁ + p₂, [H₁ H₂]⟩` (4a), `L⟨p, H⟩ = ⟨Lp, LH⟩` (4b), `⟨p, H⟩ ⊆ ⟨p, H̄⟩`, `H̄` diagonal with the absolute row sums (4c). | n/a — restated; tracked as `Sec. 2` on [Girard 2005](../2005/girard-hscc-reachability-zonotopes.md) (4a, 4b), the interval hull (4c) as `Sec. 3.4` there | `restated` |
| `Property 4` | `Box(⟨p, H⟩) = [a, b]`, `aᵢ = pᵢ - Σ_{j=0}^m \|Hᵢⱼ\|`, `bᵢ = pᵢ + Σ_{j=0}^m \|Hᵢⱼ\|` (Eq. 5). | [`IntervalEqHull.lean`](../../src/CORALean/ContSet/Zonotope/Real/Theorems/IntervalEqHull.lean), [`IntervalAttained.lean`](../../src/CORALean/ContSet/Zonotope/Real/Theorems/IntervalAttained.lean) — `Zonotope.interval` is the hull, its bounds attained | `underspecified` — the sums run from `j = 0`; the generators are `j = 1, …, m` |
| `Lemma 1` | (Bounded real lemma, from Xu and Lam's monograph) `x₊ = Ax + Bu`, `y = Cx + Du` is stable with `‖G‖∞ < γ` iff some `P ≻ 0` satisfies Eq. 7. | n/a — restated from S. Xu and J. Lam, *Robust Control and Filtering of Singular Systems* (Springer, 2006), which has no page here; `Thm. 1` is proved without it | `restated` |
| `Eq. 8` | The system `x_{k+1} = A x_k + B u_k + E w_k`, `y_k = C x_k + F v_k`. | n/a — the paper's setting | `not-a-claim` |
| `Eq. 9` | `\|x₀ - p₀\| ≤ x̄`, `\|w_k\| ≤ w̄`, `\|v_k\| ≤ v̄`, i.e. `x₀ ∈ ⟨p₀, H₀⟩`, `w_k ∈ W = ⟨0, D_w⟩`, `v_k ∈ V = ⟨0, D_v⟩`. | n/a — the paper's setting; the formalization takes any zonotopes `X₀`, `W`, `V` | `not-a-claim` |
| `Eq. 10` | The Luenberger observer `x̂_{k+1} = A x̂_k + B u_k + L(y_k - C x̂_k)`. | n/a — a definition, the estimate `x` of [`IntervalEstimateStep.lean`](../../src/CORALean/ContDynamics/LinearSysDT/Operations/IntervalEstimateStep.lean) | `not-a-claim` |
| `Eq. 13` | `x̲_k = x̂_k + e̲_k`, `x̅_k = x̂_k + e̅_k` bound `x_k` when `e̲_k ≤ e_k ≤ e̅_k`. | n/a — the estimate a bound of the error gives; part of `Thm. 2` | `not-a-claim` |
| `Eq. 14` | The error `e_k = x_k - x̂_k` follows `e_{k+1} = (A - LC) e_k + E w_k - L F v_k`. | [`LuenbergerErrorMemReachErrorSet.lean`](../../src/CORALean/ContDynamics/LinearSysDT/Theorems/Real/LuenbergerErrorMemReachErrorSet.lean) — the first step of the proof there | `correct` |
| `Eq. 15` | Eq. 14 as `e_{k+1} = A_e e_k + B_e d_k`, `A_e = A - LC`, `B_e = [E  -LF]`, `d_k = [w_k; v_k]`. | n/a — notation | `not-a-claim` |
| `Thm. 1` | For `γ > 0`: if `P ≻ 0` and `Y` satisfy the LMI Eq. 16, `[I - P ⋆ ⋆ ⋆; 0 -γ²I ⋆ ⋆; 0 0 -γ²I ⋆; PA - YC  PE  -YF  -P] ≺ 0`, then at `L = P⁻¹Y` the error system Eq. 15 is stable and `‖G_ed‖∞ < γ`, `G_ed(z) = (zI - A_e)⁻¹ B_e`. | [`HinfLmi.lean`](../../src/CORALean/ContDynamics/LinearSysDT/Definitions/HinfLmi.lean), [`DissipationOfHinfLmi.lean`](../../src/CORALean/ContDynamics/LinearSysDT/Theorems/Real/DissipationOfHinfLmi.lean), [`HinfOfLmi.lean`](../../src/CORALean/ContDynamics/LinearSysDT/Theorems/Real/HinfOfLmi.lean) — given a feasible `P`, `Y` (the solver is out of scope): every eigenvalue of `A_e` in the open unit disc, and some `γ' < γ` with `‖e‖ ≤ γ'‖d‖` whenever `z e = A_e e + B_e d`, `\|z\| = 1`, i.e. `σ_max(G_ed(z)) ≤ γ'` on the unit circle; through the dissipation inequality Eq. 17 with its margin, not the bounded real lemma | `correct` |
| `Eq. 20` | The gain from `min γ²` subject to Eq. 16. | n/a — the choice among feasible gains; every one is covered by `Thm. 1` | `not-a-claim` |
| `Thm. 2` | With `x̂₀ = p₀`, `x_k` lies in `[x̲_k, x̅_k]` of Eq. 13 for `[e̲_k, e̅_k] = Box((A - LC)ᵏ⟨0, H₀⟩) ⊕ ⨁_{i<k} Box((A - LC)ⁱ E W) ⊕ ⨁_{i<k} Box((A - LC)ⁱ(-LF) V)` (Eq. 21); in the proof this is `Box(Ω_k)`, `Ω_k` the reachable error set (Eqs. 24, 26). | [`ReachErrorSet.lean`](../../src/CORALean/ContDynamics/LinearSysDT/Definitions/ReachErrorSet.lean), [`LuenbergerErrorMemReachErrorSet.lean`](../../src/CORALean/ContDynamics/LinearSysDT/Theorems/Real/LuenbergerErrorMemReachErrorSet.lean), [`IntervalEstimateErrorEqHull.lean`](../../src/CORALean/ContDynamics/LinearSysDT/Theorems/Real/IntervalEstimateErrorEqHull.lean), [`IntervalEstimateOuter.lean`](../../src/CORALean/ContDynamics/LinearSysDT/Theorems/Real/IntervalEstimateOuter.lean) — `e_k ∈ Ω_k`, the box of Eq. 21 (computed by `Alg. 1`) is exactly `Box(Ω_k)` (Eq. 26), and `x_k` lies in the estimate, at every gain `L` | `correct` |
| `Alg. 1` | Line 2: `x̂₀ = p₀`, `D_w0 = EW`, `D_v0 = -LFV`; line 3: `S_x0 = ⟨0, H₀⟩`, `S_w0 = ∅`, `S_v0 = ∅`; per step `[e̲_k, e̅_k] = Box(S_xk) ⊕ S_wk ⊕ S_vk`, `x̲_k = x̂_k + e̲_k`, `x̅_k = x̂_k + e̅_k`, the update of `x̂`, `S_x ← (A - LC)S_x`, `S_w ← S_w ⊕ Box(D_w)`, `S_v ← S_v ⊕ Box(D_v)`, `D_w ← (A - LC)D_w`, `D_v ← (A - LC)D_v`. | [`IntervalEstimateState.lean`](../../src/CORALean/ContDynamics/LinearSysDT/Definitions/IntervalEstimateState.lean), [`IntervalEstimateStep.lean`](../../src/CORALean/ContDynamics/LinearSysDT/Operations/IntervalEstimateStep.lean), [`IntervalEstimateState.lean`](../../src/CORALean/ContDynamics/LinearSysDT/Operations/IntervalEstimateState.lean), [`IntervalEstimate.lean`](../../src/CORALean/ContDynamics/LinearSysDT/Operations/IntervalEstimate.lean), [`IntervalEstimateOuter.lean`](../../src/CORALean/ContDynamics/LinearSysDT/Theorems/Real/IntervalEstimateOuter.lean) — the listing line by line, `S_w0 = S_v0 = {0}` | `underspecified` — line 3 starts `S_w`, `S_v` at `∅`, which would make every box of line 5 empty; read as `{0}` |
| `Remark 1` | Over-approximation enters only through `Box(·)`, which Property 4 computes exactly; sums of boxes are sums of vectors. | n/a — a remark on cost and accuracy | `not-a-claim` |
| `Thm. 3` | If `P ≻ 0`, `Y` satisfy Eq. 16 and `L = P⁻¹Y`, there are `0 < α, β < 1` with `‖e_k‖ < √(β(αᵏ V₀ + γ²‖d‖²_∞/(1 - α)))` for `k ≥ 1`, `V₀ = e₀ᵀPe₀`, `‖d‖²_∞ = sup_k d_kᵀd_k` (Eq. 27). | [`ErrorBoundOfHinfLmi.lean`](../../src/CORALean/ContDynamics/LinearSysDT/Theorems/Real/ErrorBoundOfHinfLmi.lean), [`ErrorBoundOfHinfLmiCounterexample.lean`](../../src/CORALean/ContDynamics/LinearSysDT/Theorems/Real/ErrorBoundOfHinfLmiCounterexample.lean) — the bound with `≤`, `‖d‖²_∞` any bound of `d_kᵀd_k`; and the counterexample to `<` | `fixed` — the zero run `e₀ = 0`, `d ≡ 0` makes both sides `0`, at an instance where Eq. 16 holds; with `≤` it holds; see Findings |
| `Eq. 33` | `x_{k+1} = A x_k + B u_k + E w_k + L(y_k - C x_k - F v_k)`, from `y_k - C x_k - F v_k = 0`. | n/a — Eq. 8 with a zero term added, the form `Prop. 1` is built on | `not-a-claim` |
| `Prop. 1` | (From Combastel 2015) If `x_k ∈ ⟨p_k, H_k⟩` then `x_{k+1} ∈ ⟨p_{k+1}, H_{k+1}⟩`, `p_{k+1} = (A - LC)p_k + Bu_k + Ly_k`, `H_{k+1} = [(A - LC)H̄_k  E  -LF]` (Eq. 34), `H̄_k = ↓_{q,W} H_k`. | n/a — restated from C. Combastel, "Zonotopes and Kalman observers: gain optimality under distinct uncertainty paradigms and robust convergence" (Automatica, 2015), which has no page here; the set-propagation observer it describes is `observePropagation` (Eq. 6 on [Althoff 2021](../2021/althoff-arch-state-estimation.md)) | `restated` |
| `Eq. 35` | The box of `⟨p_k, H_k⟩`, `x̲ᶻ_k(i) = p_k(i) - Σ_{i=0}^s \|H_k(i, j)\|`, `x̅ᶻ_k(i)` alike, bounds `x_k`. | [`IntervalEqHull.lean`](../../src/CORALean/ContSet/Zonotope/Real/Theorems/IntervalEqHull.lean) — `Property 4` at the zonotope of `Prop. 1` | `underspecified` — the sum runs over `i = 0, …, s`; it is over the columns `j = 1, …, s` |
| `Remark 2` | `↓_{q,W}` sorts the columns by `hᵀWh` and replaces all but the `q - n_x` largest by the diagonal `H⁻ᵢᵢ = Σ_{j>q-n_x} H̃ᵢⱼ`, so that `⟨0, H_k⟩ ⊆ ⟨0, H̄_k⟩`. | [`ReduceRowSumCounterexample.lean`](../../src/CORALean/ContSet/Zonotope/Real/Theorems/ReduceRowSumCounterexample.lean) — the counterexample; with `\|H̃ᵢⱼ\|` the inclusion holds at every split of the columns, `Zonotope.reduceBy_outer` | `fixed` — without absolute values the row sum cancels: `H = [1 -1]`, `q = n_x = 1` gives `H⁻ = 0`; see Findings |
| `Eq. 36` | The interval observer `x̅ⁱ_{k+1} = A x̅ⁱ_k + Bu_k + L(y_k - C x̅ⁱ_k) + d̅`, `x̲ⁱ_{k+1}` alike with `d̲`. | n/a — a definition, [`IntervalObserver.lean`](../../src/CORALean/ContDynamics/LinearSysDT/Operations/IntervalObserver.lean) | `not-a-claim` |
| `Eq. 37` | `d̅ = E⁺w̅ - E⁻w̲ + (-LF)⁺v̅ - (-LF)⁻v̲`, `d̲ = E⁺w̲ - E⁻w̅ + (-LF)⁺v̲ - (-LF)⁻v̅`. | n/a — a definition, [`IntervalObserver.lean`](../../src/CORALean/ContDynamics/LinearSysDT/Operations/IntervalObserver.lean) | `not-a-claim` |
| `Lemma 2` | (After Efimov et al.) `x̲ ≤ x ≤ x̅` gives `A⁺x̲ - A⁻x̅ ≤ Ax ≤ A⁺x̅ - A⁻x̲`, `A⁺ = max{0, A}`, `A⁻ = A⁺ - A`. | [`MulVecPosNegBounds.lean`](../../src/CORALean/Global/MulVecPosNegBounds.lean) | `correct` |
| `Lemma 3` | (After Efimov and Raïssi) `x_{k+1} = A x_k + w_k` with `A ≥ 0`, `w_k ≥ 0` stays nonnegative from `x₀ ≥ 0`. | [`NonnegOfNonnegRecurrence.lean`](../../src/CORALean/Global/NonnegOfNonnegRecurrence.lean) | `correct` |
| `Thm. 4` | If `A - LC ≥ 0` and `x̲ⁱ₀ ≤ x₀ ≤ x̅ⁱ₀`, the observer Eq. 36 gives `x̲ⁱ_k ≤ x_k ≤ x̅ⁱ_k` for all `k`. | [`IntervalObserver.lean`](../../src/CORALean/ContDynamics/LinearSysDT/Operations/IntervalObserver.lean), [`IntervalObserverOuter.lean`](../../src/CORALean/ContDynamics/LinearSysDT/Theorems/Real/IntervalObserverOuter.lean) — `w̲ ≤ w_k ≤ w̅`, `v̲ ≤ v_k ≤ v̅` | `correct` |
| `Eq. 41` | (From Efimov and Raïssi) The LMIs `[P  PA - YC; ⋆  P] ≻ 0`, `P ≻ 0` diagonal, `PA - YC ≥ 0` give a gain with `A - LC` nonnegative and Schur. | n/a — restated from D. Efimov and T. Raïssi, "Design of interval observers for uncertain dynamical systems" (Automation and Remote Control, 2016), which has no page here | `restated` |
| `Thm. 5` | (Modified from Efimov et al. 2013) If `A - LC` is Schur and `R = S(A - LC)S⁻¹ ≥ 0` for an invertible `S`, then `x̲ᵗ_k ≤ x_k ≤ x̅ᵗ_k` for the observer Eq. 42 with Eq. 43, provided `x̲ᵗ₀ ≤ x₀ ≤ x̅ᵗ₀`. | [`IntervalObserverCoord.lean`](../../src/CORALean/ContDynamics/LinearSysDT/Operations/IntervalObserverCoord.lean), [`IntervalObserverTransformed.lean`](../../src/CORALean/ContDynamics/LinearSysDT/Operations/IntervalObserverTransformed.lean), [`IntervalObserverTransformedOuter.lean`](../../src/CORALean/ContDynamics/LinearSysDT/Theorems/Real/IntervalObserverTransformedOuter.lean) — the Schur property is not needed for the enclosure | `correct` |
| `Lemma 4` | (From Efimov et al. 2013) If `(A - LC, e₁)` and `(R, e₂)` are observable and `R` has the eigenvalues of `A - LC`, then `R = S(A - LC)S⁻¹` for some `S`. | n/a — restated from D. Efimov, W. Perruquetti, T. Raïssi and A. Zolghadri, "On interval observer design for time-invariant discrete-time systems" (ECC 2013), which has no page here | `restated` |
| `Eq. 48` | (From Raïssi, Efimov and Zolghadri) `S = O_R⁻¹ O_{A-LC}`, the observability matrices. | n/a — restated from T. Raïssi, D. Efimov and A. Zolghadri, "Interval state estimation for a class of nonlinear systems" (IEEE TAC, 2012), which has no page here | `restated` |
| `Thm. 6` | With the same `L`, `x̂₀ = p₀` and `Ω₀ = ⟨0, H₀⟩`, `x̅ᶻ_k ≥ x̅_k` and `x̲ᶻ_k ≤ x̲_k`: Alg. 1 is tighter than the zonotope method Eq. 34. | [`IntervalEstimateLeZonotope.lean`](../../src/CORALean/ContDynamics/LinearSysDT/Theorems/Real/IntervalEstimateLeZonotope.lean), [`IntervalEstimateLeOfBounds.lean`](../../src/CORALean/ContDynamics/LinearSysDT/Theorems/Real/IntervalEstimateLeOfBounds.lean), [`ReachErrorSetSuccSubset.lean`](../../src/CORALean/ContDynamics/LinearSysDT/Theorems/Real/ReachErrorSetSuccSubset.lean) — for every zonotope sequence with `X₀ ⊆ Z₀` and `Z_{k+1} ⊇ (A - LC)Z_k ⊕ (Bu_k + Ly_k) ⊕ EW ⊕ (-LF)V`, which Eq. 34 is at every outer reduction | `underspecified` — Eq. 34b prints the generators `E`, `-LF` for the sets `⟨0, D_w⟩`, `⟨0, D_v⟩` of Eq. 9; read as `E D_w`, `-LF D_v`, as the proof's Eq. 50 uses them |
| `Lemma 5` | For `I = [a, b]` and `A ≥ 0`, `Box(AI) = AI = [Aa, Ab]`. | [`HullImageOfNonneg.lean`](../../src/CORALean/ContSet/Interval/Real/Theorems/HullImageOfNonneg.lean), [`ImageOfNonnegCounterexample.lean`](../../src/CORALean/ContSet/Interval/Real/Theorems/ImageOfNonnegCounterexample.lean) — `Box(AI) = [Aa, Ab]`; and the counterexample to `AI = [Aa, Ab]` | `fixed` — `A = [1 1; 1 1]` maps `[0, 1]²` onto a segment, not the box `[0, 2]²`; the hull equality holds and is what the proof of `Thm. 7` uses; see Findings |
| `Thm. 7` | With the same `L` and `x̲ⁱ₀ = x̲₀`, `x̅ⁱ₀ = x̅₀`, `x̅ⁱ_k ≥ x̅_k` and `x̲ⁱ_k ≤ x̲_k`: Alg. 1 is tighter than the interval observer Eq. 36. | [`IntervalEstimateLeIntervalObserver.lean`](../../src/CORALean/ContDynamics/LinearSysDT/Theorems/Real/IntervalEstimateLeIntervalObserver.lean), [`IntervalEstimateLeOfBounds.lean`](../../src/CORALean/ContDynamics/LinearSysDT/Theorems/Real/IntervalEstimateLeOfBounds.lean) — `A - LC ≥ 0`, `W ⊆ [w̲, w̅]`, `V ⊆ [v̲, v̅]` | `underspecified` — the hypothesis `A - LC ≥ 0` of `Thm. 4`, which the proof uses, is missing from the statement; without it the inequality fails (`A - LC = -1`); see Findings |
| `Remark 3` | The interval observer Eq. 36 is the Luenberger estimate plus an approximated error bound, an outer approximation of Alg. 1's. | n/a — a remark, by `Thm. 7` | `not-a-claim` |
| `Thm. 8` | With the same `L` and `x̲ᵗ₀ = x̲₀`, `x̅ᵗ₀ = x̅₀`, `x̅ᵗ_k ≥ x̅_k` and `x̲ᵗ_k ≤ x̲_k`: Alg. 1 is tighter than the interval observer Eq. 42. | [`IntervalEstimateLeIntervalObserverTransformed.lean`](../../src/CORALean/ContDynamics/LinearSysDT/Theorems/Real/IntervalEstimateLeIntervalObserverTransformed.lean), [`IntervalEstimateLeOfBounds.lean`](../../src/CORALean/ContDynamics/LinearSysDT/Theorems/Real/IntervalEstimateLeOfBounds.lean) — `S` invertible, `R ≥ 0`, `W ⊆ [w̲, w̅]`, `V ⊆ [v̲, v̅]` | `underspecified` — the hypotheses of `Thm. 5` (`S` invertible, `R ≥ 0`), under which Eq. 42 is defined and an interval observer and which the proof's Eq. 71 uses, are missing from the statement |
| `Remark 4` | The two sources of conservatism in Eq. 42: `P̃ ⊇ P` (Eq. 74) and `Box(Ω_k) ⊆ Box(P̃)` (Eq. 80). | n/a — a remark | `not-a-claim` |
| `Sec. VII` | A DC servo motor and a second-order example: bounds of Alg. 1, the zonotope method and the interval observers (Figs. 1-5). | n/a — an experiment | `not-a-claim` |

## Findings

**`Thm. 3` — the strict bound fails at the zero run.** Eq. 27 claims `0 < α, β < 1` with
`‖e_k‖ < √(β(αᵏ V₀ + γ²‖d‖²_∞/(1 - α)))` for every `k ≥ 1`. The run `e₀ = 0`, `d ≡ 0` solves every
error system and makes both sides `0`. The strict steps of the proof (Eqs. 28, 29, 31, 32 and
`α₁ eᵀe < eᵀPe`) all need `(e_k, d_k) ≠ 0`. At `A = 0`, `C = E = F = 1`, `γ = 2`, `P = 2`,
`Y = 0`, Eq. 16 holds, so the claim is not vacuous there
([`ErrorBoundOfHinfLmiCounterexample.lean`](../../src/CORALean/ContDynamics/LinearSysDT/Theorems/Real/ErrorBoundOfHinfLmiCounterexample.lean)).
With `≤` it holds, with `α = 1 - 1/α₂`, `β = 1/α₁`, `α₁ > 1` from the margin of Eq. 17 and `α₂`
any bound of `P`
([`ErrorBoundOfHinfLmi.lean`](../../src/CORALean/ContDynamics/LinearSysDT/Theorems/Real/ErrorBoundOfHinfLmi.lean)).

**`Remark 2` — the boxed columns need absolute values.** `H⁻ᵢᵢ = Σ_{j=q-n_x+1}^s H̃ᵢⱼ` is the
signed row sum of the dropped columns, which can cancel: in one dimension `H = [1  -1]` with
`q = n_x = 1` keeps no column and gives `H⁻ = 0`, and `⟨0, [0]⟩ = {0}` misses `2 ∈ ⟨0, H⟩`
([`ReduceRowSumCounterexample.lean`](../../src/CORALean/ContSet/Zonotope/Real/Theorems/ReduceRowSumCounterexample.lean)).
Property 3's (4c), which the remark appeals to, has the absolute values, and with them the
inclusion holds at every split (`Zonotope.reduceBy_outer`).

**`Lemma 5` — the image of a box is not a box.** `AI = [Aa, Ab]` fails for `A = [1 1; 1 1]` and
`I = [0, 1]²`: `AI` is the segment from `0` to `(2, 2)`, which misses `(2, 0)`
([`ImageOfNonnegCounterexample.lean`](../../src/CORALean/ContSet/Interval/Real/Theorems/ImageOfNonnegCounterexample.lean)).
`Box(AI) = [Aa, Ab]` holds
([`HullImageOfNonneg.lean`](../../src/CORALean/ContSet/Interval/Real/Theorems/HullImageOfNonneg.lean)), and the
proof of `Thm. 7` only needs that: its Eqs. 59 and 61 read as equalities of boxes.

**`Thm. 7` and `Thm. 8` — the compared observer must be one.** Both theorems state only "the same
observer gain and initial conditions". The proof of `Thm. 7` uses `A - LC ≥ 0` (Lemma 5 at
`A - LC`), and without it the inequality fails: in one dimension with `A - LC = -1`, `H₀ = h > 0`
and symmetric noise bounds `±δ`, Eq. 36 gives `x̅ⁱ₁ - x̂₁ = -h + δ` while Alg. 1 gives `h + δ`.
`Thm. 8`'s proof uses `R ≥ 0` the same way (its Eq. 71 is Eq. 63 for the transformed system).
Both are the conditions under which the compared method is an interval observer at all
(`Thm. 4`, `Thm. 5`); the formalization assumes them.

**`Alg. 1` seeds the error correctly; CORA does not.** Line 3 starts `S_x` at `⟨0, H₀⟩`, the
initial error set for `x̂₀ = p₀`. CORA's `priv_observe_interval`, which cites this paper for
`Hinf-G`, starts it at `R0` itself (FINDINGS.md, `LinearSysDT.observeInterval_cora_counterexample`),
as does the restatement in Althoff's ARCH21 paper ([Althoff 2021](../2021/althoff-arch-state-estimation.md));
the paper is not the source of that error.
