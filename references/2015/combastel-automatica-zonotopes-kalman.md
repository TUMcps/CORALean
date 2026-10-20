# Zonotopes and Kalman observers: Gain optimality under distinct uncertainty paradigms and robust convergence

C. Combastel. "Zonotopes and Kalman observers: Gain optimality under distinct uncertainty paradigms and robust convergence". Automatica, 55:265-273, 2015.

**Source:** the published article (Automatica 55 (2015) 265-273, doi:10.1016/j.automatica.2015.03.008, 9 pages), provided by the user and read in full; text extracted with PyMuPDF.  
**Inventory:** confirmed (the numbered statements share one counter: Prop. 1, Defs. 2-4, Thm. 5, Cor. 6, Thm. 7, Lemma 8, Assumption 9, Thms. 10-12, Prop. 13 in App. A; equations (1)-(55), (A.1), (B.1)-(B.2), (D.1). An equation printed inside a statement or its proof is covered by that statement's row; the equations of the ZKF iteration, of the stochastic Kalman filter and of the example are grouped under `Sec. 5`, `Sec. 6` and `Sec. 8`)

The observer behind CORA's `FRad-C`: the zonotope `⟨c, R⟩` of the state is propagated through
`R₊ = [(A - G C) ↓R, E, -G F]` (`Prop. 1`), and the gain `G* = A P̄ Cᵀ (C P̄ Cᵀ + F Fᵀ)⁻¹` that
minimizes the F-radius `‖R₊‖_F` of the next zonotope is the Kalman gain with the covariation
`P̄ = R̄ R̄ᵀ` in place of the covariance (`Thm. 5`). The gain's optimality in the unweighted
Frobenius norm is formalized (`Zonotope.luenbergerGain_optimal`), and so are the two radii; the
weighted optimality, the covariation recursion and the robust-convergence analysis of Sec. 7 are
not. `Lemma 8` is false as printed (under Findings), which the later results do not inherit,
since `Assumption 9` bounds the Lyapunov matrices from below.

## Results

| Result | What it says | In CORALean | Class |
|---|---|---|---|
| `Sec. 2.1` | Matrix-calculus background quoted from Boyd et al. (1994) and Golub and Van Loan (1996): spd matrices and their inverses, the Schur complement criterion `[A, B; Bᵀ, C] ≻ 0 ⇔ A ≻ 0 ∧ A - B C⁻¹ Bᵀ ≻ 0`, `tr(Rᵀ M R) > 0` for `M` spd and `R` with nonzero columns, and the weighted Frobenius norm `‖R‖_{F,W} = √tr(Rᵀ W R)`, `‖R‖²_{F,W} = Σᵢ ‖rᵢ‖²_W`. | n/a — restated from the two textbooks, which have no page here | `restated` |
| `Eq. 1` | `tr(A) = tr(Aᵀ)`, `tr(AB) = tr(BA)`. | n/a — `Matrix.trace_transpose`, `Matrix.trace_mul_comm` | `mathlib` |
| `Eq. 2` | `∂_X tr(A Xᵀ B) = Aᵀ Bᵀ`, with `∂_X f = [∂f/∂X_ji]`. | n/a — restated from the matrix-calculus textbooks; used only in the proof of `Thm. 5`, which the formalization proves without derivatives | `restated` |
| `Eq. 3` | `∂_X tr(A X B Xᵀ C) = B Xᵀ C A + Bᵀ Xᵀ Aᵀ Cᵀ`. | n/a — restated as `Eq. 2` | `restated` |
| `Eq. 4` | The zonotope `⟨c, R⟩ = {c + R s : ‖s‖_∞ ≤ 1}`, invariant under permuting the columns of `R`. | n/a — restated; tracked as `Sec. 2` on [Girard 2005](../2005/girard-hscc-reachability-zonotopes.md) | `restated` |
| `Eq. 5` | `⟨c₁, R₁⟩ ⊕ ⟨c₂, R₂⟩ = ⟨c₁ + c₂, [R₁, R₂]⟩`. | n/a — restated; tracked as `Sec. 2` on [Girard 2005](../2005/girard-hscc-reachability-zonotopes.md) | `restated` |
| `Eq. 6` | `L ⊙ ⟨c, R⟩ = ⟨L c, L R⟩`. | n/a — restated; tracked as `Sec. 2` on [Girard 2005](../2005/girard-hscc-reachability-zonotopes.md) | `restated` |
| `Eq. 7` | The box enclosure `⟨c, R⟩ ⊂ ⟨c, b(R)⟩`, `b(R) = diag(\|R\| 1)`, the interval hull. | n/a — restated; tracked as `Sec. 3.4` on [Girard 2005](../2005/girard-hscc-reachability-zonotopes.md) | `restated` |
| `Eq. 8` | The reduction `↓_{q,W}` first sorts the columns of `R` by decreasing `‖rⱼ‖²_W`. | n/a — restated from Combastel (2003, 2005), weighted by `W`; the unweighted operator is tracked as `Sec. 3.2` on [Combastel 2003](../2003/combastel-ecc-state-bounding-observer.md) | `restated` |
| `Eq. 9` | If `p ≤ q`, `↓_{q,W} R = R`, else `↓_{q,W} R = [R_>, b(R_<)] ∈ ℝ^{n×q}`, with `⟨R⟩ ⊂ ⟨↓_{q,W} R⟩`. | n/a — restated as `Eq. 8` | `restated` |
| `Eq. 10` | `R_> = [r₁, …, r_{q-n}]`, `R_< = [r_{q-n+1}, …, r_p]`. | n/a — restated as `Eq. 8` | `restated` |
| `Eq. 11` | `x_{k+1} = A_k x_k + B_k u_k + E_k v_k`, `v_k ∈ ⟨0, I⟩`. | n/a — the paper's setting | `not-a-claim` |
| `Eq. 12` | `y_k = C_k x_k + D_k u_k + F_k w_k`, `w_k ∈ ⟨0, I⟩`. | n/a — the paper's setting | `not-a-claim` |
| `Eq. 13` | `x₀ ∈ ⟨c₀, R₀⟩`. | n/a — the paper's setting | `not-a-claim` |
| `Eq. 14` | `x₊ = A x + B u + E v + G (y - C x - D u - F w)` for any gain `G`, the added term being zero. | n/a — the identity behind `Prop. 1`, used in its proof | `not-a-claim` |
| `Prop. 1` | (Observer structure) For the system of Eqs. 11-13 and any gain sequence `G`, the recursion `c₊ = (A - G C) c + (B - G D) u + G y` (Eq. 15), `R₊ = [(A - G C) R̄, E, -G F]`, `R̄ = ↓_{q,W} R` (Eq. 16) keeps `x ∈ ⟨c, R⟩` (Eq. 17) for all `k ≥ 0`; the proof is the induction of Eq. 18. | — partial: [`LinearSysDT.observePropagation_outer`](../../src/CORALean/ContDynamics/LinearSysDT/Theorems/Real/ObservePropagationOuter.lean), the same induction with constant matrices, `D = 0`, a gain that is a function of the current set and the reduction after the step; missing: the time-varying matrices `A_k`, …, `F_k`, the gain sequence and the feedthrough `D_k u_k` | — |
| `Def. 2` | (FW-radius) For `W = Wᵀ ≻ 0`, the FW-radius of `⟨c, R⟩` is `‖⟨c, R⟩‖_{F,W} = ‖R‖_{F,W}`. | [`FWRadius.lean`](../../src/CORALean/ContSet/Zonotope/Real/Definitions/FWRadius.lean) — `Zonotope.fwRadius W Z = √Σⱼ gⱼᵀ W gⱼ`, which is `√tr(Rᵀ W R)` | `correct` |
| `Def. 3` | (F-radius) The F-radius of `⟨c, R⟩` is `‖R‖_F`, the FW-radius at `W = I`. | [`FWRadius.lean`](../../src/CORALean/ContSet/Zonotope/Real/Definitions/FWRadius.lean) — `Zonotope.fwRadius 1`, `√Σⱼ gⱼᵀ gⱼ`, as the definition itself puts it | `correct` |
| `Def. 4` | (Covariation) `cov(⟨c, R⟩) = R Rᵀ`; minimizing the F-radius of `⟨c₊, R₊⟩` is minimizing `tr(R₊ R₊ᵀ)`. | — | — |
| `Eq. 19` | `P = R Rᵀ`, `Q_v = E Eᵀ`, `Q_w = F Fᵀ`. | n/a — notation | `not-a-claim` |
| `Eq. 20` | `P̄ = R̄ R̄ᵀ = cov(↓_{q,W} R)`. | n/a — notation | `not-a-claim` |
| `Thm. 5 (F-radius)` | (Optimal observer gain) For `R₊` of Eq. 16, the gain `G* = A K*`, `K* = L S⁻¹` (Eq. 21), `L = P̄ Cᵀ`, `S = C P̄ Cᵀ + Q_w` (Eq. 22) minimizes the F-radius `‖R₊‖_F` of `⟨c₊, R₊⟩`, that is `tr(P₊)`. | [`LuenbergerGain.lean`](../../src/CORALean/ContSet/Zonotope/Real/Operations/LuenbergerGain.lean), [`LuenbergerGainOptimal.lean`](../../src/CORALean/ContSet/Zonotope/Real/Theorems/LuenbergerGainOptimal.lean) — `Zonotope.luenbergerGain_optimal`: with `A, C, E, F, R̄` as `F, Γ, Q, R, Ĝ`, the squared Frobenius norm of the step's generators at any gain `G'` is the one at `G*` plus `‖(G' - G*) C R̄‖²_F + ‖(G' - G*) F‖²_F`, so `G*` attains the minimum; `Ḡ` lists the blocks of `R₊` in another order | `underspecified` — `S = C P̄ Cᵀ + F Fᵀ` is inverted without being assumed invertible, and may be singular when `F Fᵀ` is (`F` with fewer columns than rows); the formalization supplies the invertibility |
| `Thm. 5 (FW-radius)` | The same `G*` minimizes `‖R₊‖²_{F,W}` for every `W = Wᵀ ≻ 0`: it does not depend on `W`. | — | — |
| `Eq. 21` | `G* = A K*`, `K* = L S⁻¹`. | n/a — inside `Thm. 5 (F-radius)`, whose row covers it | `not-a-claim` |
| `Eq. 22` | `L = P̄ Cᵀ`, `S = C P̄ Cᵀ + Q_w`. | n/a — inside `Thm. 5 (F-radius)`, whose row covers it | `not-a-claim` |
| `Sec. 5` | (Zonotopic Kalman filter, Eqs. 23-31) `R̄ = ↓_{q,W} R`, `P̄ = P - R_< R_<ᵀ + b(R_<)²`, the innovation `ε = y - (C c + D u)`, `K* = P̄ Cᵀ (C P̄ Cᵀ + Q_w)⁻¹`, `c̃ = c + K* ε`, `G* = A K*`, `c₊ = A c̃ + B u`, `R₊ = [(A - G* C) R̄, E, -G* F]`, `P₊ = Ă P̄ Ăᵀ + Ĕ Ĕᵀ`; it computes `c₊`, `R₊` as `Prop. 1` at `G = G*`, so `x ∈ ⟨c, R⟩` holds. | — partial: [`LinearSysDT.observePropagation`](../../src/CORALean/ContDynamics/LinearSysDT/Operations/ObservePropagation.lean), [`LinearSysDT.observePropagation_outer`](../../src/CORALean/ContDynamics/LinearSysDT/Theorems/Real/ObservePropagationOuter.lean), the centers and generators at any gain function, so at `Zonotope.luenbergerGain`, and their enclosure; missing: the covariation recursion `P̄`, `P₊` of Eqs. 24 and 31, the weighted reduction and the time-varying matrices | — |
| `Eq. 32` | `x ∈ c ± r`, `r = \|R\| 1`, the interval bounds from the zonotope by Eq. 7. | n/a — restated; tracked as `Sec. 3.4` on [Girard 2005](../2005/girard-hscc-reachability-zonotopes.md) | `restated` |
| `Cor. 6` | At `G = G*`, `P₊ = Ă P̄ Ăᵀ + Q_v + G* Q_w G*ᵀ`, `Ă = A - G* C` (Eq. 33), equals `A P̃ Aᵀ + Q_v`, `P̃ = (I - K* C) P̄` (Eq. 34). | — | — |
| `Sec. 6` | The stochastic Kalman filter in one-step-ahead form, Eqs. 35-38, for Gaussian `v`, `w`, `x₀`, and the facts (i)-(iv) comparing it with the ZKF. | n/a — stochastic estimation with Gaussian random vectors, a subject CORALean does not cover | `not-covered` |
| `Thm. 7` | (ZKF vs. KF) With equal `c₀`, `P₀ = R₀ R₀ᵀ` equal to the covariance and `q → ∞` (no reduction), ZKF and KF give for all `k` the same gain `K*`, the same center `c` and equal covariation and covariance `P`. | n/a — a comparison with the stochastic Kalman filter of `Sec. 6`, a subject CORALean does not cover | `not-covered` |
| `Lemma 8` | `x_{k+1} = A_k x_k` is γ-stable if there are a bounded sequence of spd `W_k` and `γ ∈ (0, 1]` with `[γ W_k, A_kᵀ W_{k+1}; ⋆, W_{k+1}] ≻ 0` (Eq. 39) for all `k`; the proof shows `V_{k+1} < γ V_k` for `V_k = x_kᵀ W_k x_k`. | — | — |
| `Assumption 9` | (Robust detectability) Bounded gains `G_k` and spd `W_k` with eigenvalues in a fixed `[λ, λ̄]`, `λ > 0`, are designed so that `x_{k+1} = (A_k - G_k C_k) x_k` is robustly γ-stable, `γ < 1`, with `W_k` as Lyapunov matrices. | n/a — an assumption of `Thm. 11` and `Thm. 12` | `not-a-claim` |
| `Thm. 10` | For `W` spd with eigenvalues in `[λ, λ̄]`, `n ≤ q < p`, `R̄ = ↓_{q,W} R`, `d = p - q`, `μ = ((λ̄/λ)(d + n) - 1)(d + n)`: `‖R̄‖²_{F,W} - ‖R‖²_{F,W} ≤ (μ/(d + q)) ‖R‖²_{F,W}` (Eq. 40); proof in App. B, Eqs. B.1-B.2. | — | — |
| `Thm. 11` | Under `Assumption 9`, with bounded `E_k`, `F_k` of fixed size, ZKF keeps `x_k ∈ ⟨c_k, R_k⟩` (Eq. 41), has a `q₀` such that for `q ≥ q₀` the FW-radii `‖R_k‖²_{F,W_k}` are bounded (Eq. 42), and `p_{R_k} ≤ q + p_E + p_F` for `k > 0` (Eq. 43). | — | — |
| `Thm. 12` | Under the same assumptions there is a bounded `ψ_k ≥ ‖E_k‖²_{F,W_{k+1}} + ‖G_k F_k‖²_{F,W_{k+1}}` (Eq. 44), and with `γ̄ = γ (1 + μ/(d + q))`, `ϕ_k = ‖R_k‖²_{F,W_k}` (Eq. 45), `ϕ_{k+1} ≤ γ̄ ϕ_k + ψ_k` and `ϕ_∞ ≤ ψ̄/(1 - γ̄)` (Eq. 46); proof in App. C. | — | — |
| `Sec. 8` | The numerical example, Eqs. 47-55: a gain-scheduled LPV system, the LMI design of `W` and `G(α)` by `Prop. 13`, Table 1 and Figs. 1-3. | n/a — an experiment | `not-a-claim` |
| `Prop. 13` | (App. A) If spd `W_k`, `Y_k`, `Z_k` and `γ ∈ (0, 1]` satisfy `[γ W_k, A_kᵀ Y_k - C_kᵀ Z_k; ⋆, Y_k + Y_kᵀ - W_{k+1}] ≻ 0` (Eq. A.1), then `x_{k+1} = (A_k - G_k C_k) x_k` with `G_k = (Z_k Y_k⁻¹)ᵀ` is γ-stable with `W_k` as Lyapunov matrices. | — | — |
| `App. D` | The flop count of one ZKF iteration under constant `W`, Eq. D.1, linear in `q`, against the `O(q³)` of an svd-based correction. | n/a — a running time | `not-a-claim` |

## Findings

**`Lemma 8` is false as printed.** The hypothesis bounds `W_k` above but not below, and the
conclusion rests on `V_{k+1} < γ V_k` alone, which says nothing of `x_k` once `W_k` may shrink
to zero. Take the scalar system `A_k = 2`, any `γ ∈ (0, 1]` and `W_k = (γ/8)ᵏ`: `W_k > 0`,
`W_k ≤ 1`, and Eq. 39 holds, since `W_{k+1} > 0` and `γ W_k - 4 W_{k+1} = (γ/8)ᵏ γ/2 > 0`; yet
`x_k = 2ᵏ x₀` diverges. The lemma needs `W_k ≽ λ I` for a fixed `λ > 0`, which `Assumption 9`
supplies (its eigenvalues lie in `[λ, λ̄]`, `λ > 0`), so `Thm. 11` and `Thm. 12`, which use the
lemma only under `Assumption 9`, are not affected. `Prop. 13`, whose conclusion is `Lemma 8`'s,
needs the same bound. The row stays `—` until it is formalized.

**Misprints in the setting and in `Thm. 11`.** None changes a result.

* Sec. 3 writes `v_k ∈ [-1, +1]^{n_w} = ⟨0, I_{n_v}⟩`; `v_k ∈ ℝ^{n_v}`, so the box is
  `[-1, +1]^{n_v}`.
* `Thm. 11` takes `F_k ∈ ℝ^{n_x × p_F}`. `F_k` multiplies the measurement noise in Eq. 12,
  `y_k ∈ ℝ^{n_y}`, so `F_k ∈ ℝ^{n_y × p_F}`.
* Sec. 6 writes the covariance of the predicted state as `(A - G C) P (A - G C) + Q_v + G Q_w Gᵀ`;
  the first term is `(A - G C) P (A - G C)ᵀ`, as in the proof of `Thm. 5`.
