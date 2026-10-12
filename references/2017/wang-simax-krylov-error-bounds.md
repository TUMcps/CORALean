# Error bounds for the Krylov subspace methods for computations of matrix exponentials

H. Wang, Q. Ye. "Error bounds for the Krylov subspace methods for computations of matrix exponentials". SIAM Journal on Matrix Analysis and Applications, 38(1):155-187, 2017.

**Source:** https://arxiv.org/pdf/1603.07358 (arXiv:1603.07358v1, 23 Mar 2016, 33 pages, the only version, read in full; text extracted with `pypdf`). The typeset SIAM article (doi:10.1137/16M1075454) was not reachable, so the arXiv text may differ from it in numbering, constants and proofs; numbering below is the arXiv version's. CORA's `linearSys/private/priv_subspace_Krylov_individual_Wang.m` cites "Theorem 3.1 of [1]".  
**Inventory:** unconfirmed (arXiv v1 only: Theorems 2.1, 3.1, 5.1, 5.2, 6.1, Propositions 2.2, Lemmas 4.1-4.5, Corollaries 5.3, 5.4, Examples 1-4, equations (1.1)-(7.3), Tables 1-3, Figures 1-5; no Definitions or Algorithms; the rows below are the results and the numbered displays that make a claim)

An a posteriori bound for the Arnoldi approximation `V_k e^{-τH_k}e₁` of `e^{-τA}v`, for **any**
`A ∈ ℂⁿˣⁿ` (`Thm. 3.1`): the error is at most `h_{k+1,k}e^{-min{ν(A),0}τ}∫₀^τ|h(t)|dt`,
`h(t) = e_k*e^{-tH_k}e₁`, `ν(A) = min Re W(A) = λ_min((A + A*)/2)`; no nonexpansive hypothesis, the
price being the factor `e^{-min{ν,0}τ}`. A priori bounds follow from the decay of `h` by Faber
polynomials and a conformal map of the rectangle `[a, b] × [-c, c]` enclosing `W(A)`
(`Thm. 5.1`, `Thm. 5.2`), and for skew-Hermitian `A = -iH` through the Lanczos relation
(`Thm. 6.1`). CORA's `priv_subspace_Krylov_individual_Wang` evaluates a quadrature of the weighted
integrand of the proof of `Thm. 3.1`; **it has no caller**: `grep` over `~/CORA` finds the name only in its
own file, and `priv_initReach_Krylov` and `priv_inputSolution_Krylov` use the Jawecki routine,
`priv_subspace_Krylov_Saad` the Saad one (the comment `nu_A_test ... %<-- for Wang approx.` in `priv_subspace_Krylov_Saad` is all that
remains of a call), so the routine is unreachable from `linearSys` methods. Formalized: `Thm. 3.1` itself
with its weighted form, under `Re(x*Ax) ≥ ν x*x` and the Krylov identity (3.1) alone, the contraction
estimate (3.5) behind it, its first-inequality form for Lanczos (6.4), and the last step of `Thm. 5.2`
from a decay bound on `h`. The a priori bounds need Faber series, Crouzeix's theorem and Jacobi
elliptic functions, which Mathlib lacks.

## Results

| Result | What it says | In CORALean | Class |
|---|---|---|---|
| `Thm. 2.1` | (Faber approximation, [13, Cor. 2.2]) For a closed Jordan region `D` of bounded total rotation `V` and `f` analytic in `I(C_R)`: `‖f - Π_N‖_∞ ≤ M(R)V/π (ρ/R)^{N+1}/(1 - ρ/R)` (2.4), and the same with the unit-disk normalization (2.5). | n/a — restated from Ellacott 1983 [13, Cor. 2.2] | `restated` |
| `Prop. 2.2` | Properties of the Jacobi elliptic integrals `K`, `E` and of `sn`, `cn`, `dn`: derivatives (2.9), (2.10), the limit (2.11), periodicity (2.12), (2.13), derivatives (2.14)-(2.16), addition formulas (2.17)-(2.19), and the sign Tables 1-3 on `[-K, K] × [0, 2iK']`. | n/a — restated from Abramowitz and Stegun [1], Markushevich [19] and Lawden [21]; CORALean has no Jacobi elliptic functions | `restated` |
| `Eq. 3.1` | (Arnoldi relation) `AV_k = V_kH_k + h_{k+1,k}v_{k+1}e_k^T`, `V_k` orthonormal, `H_k` upper Hessenberg, `h_{k+1,k} ≥ 0`. | n/a — restated from Saad 1992 [27]; the relation is the hypothesis of every theorem below, as in [Jawecki et al. 2020](../2020/jawecki-bit-krylov-error-bounds.md) (2.2) | `restated` |
| `Eq. 3.2` | `h²_{k+1,k} = ‖Av_k‖² - Σ_i h²_{i,k} ≤ ‖A‖²`. | — | — |
| `Eq. 3.4` | `µ(A) = λ_max((A + A*)/2)`, `ν(A) = λ_min((A + A*)/2)` for the logarithmic norm `µ(A) = max Re W(A)` and `ν(A) = -µ(-A)`. | — | — |
| `Eq. 3.5` | `‖e^{tA}‖ ≤ e^{tµ(A)}` for `t ≥ 0`, attributed to Dahlquist [9] and Söderlind [28]. | n/a — restated from Dahlquist [9] and Söderlind [28]; the vector form for `-A`, `‖e^{r(-A)}x‖₂ ≤ e^{-rν}‖x‖₂` under `Re(x*Ax) ≥ ν x*x`, is [`NormExpNegSmulMulVecLe.lean`](../../src/CORALean/ContDynamics/LinearSys/Krylov/Theorems/NormExpNegSmulMulVecLe.lean), through `W(-A + ν) ⊆ ℂ⁻` and [`NormExpSmulMulVecLe.lean`](../../src/CORALean/ContDynamics/LinearSys/Krylov/Theorems/NormExpSmulMulVecLe.lean) | `restated` |
| `Thm. 3.1` | (A posteriori bound) For `A ∈ ℂⁿˣⁿ`, `‖v‖ = 1`, Arnoldi `V_k`, `H_k` with (3.1) and `w_k(τ) = V_ke^{-τH_k}e₁`: `‖w(τ) - w_k(τ)‖ ≤ h_{k+1,k}e^{-min{ν(A),0}τ}∫₀^τ\|h(t)\|dt` (3.6), `h(t) = e_k^Te^{-tH_k}e₁` (3.7). | [`ErrorLeExpMinIntegralDelta.lean`](../../src/CORALean/ContDynamics/LinearSys/Krylov/Theorems/ErrorLeExpMinIntegralDelta.lean) — for `τ ≥ 0`, any `A`, the Krylov identity (3.1) and `v = V_ke₁`, from the weighted bound of the proof, `h_{k+1,k}∫₀^τ\|h(t)\|e^{(t-τ)ν}dt` ([`ErrorLeIntegralDeltaExpWeight.lean`](../../src/CORALean/ContDynamics/LinearSys/Krylov/Theorems/ErrorLeIntegralDeltaExpWeight.lean)), which CORA's routine quadratures, through the error integral (2.8) and the defect (2.9) of Jawecki et al. **As printed:** `ν` is any real with `Re(x*Ax) ≥ ν x*x` for all `x`, which `ν(A)` is the largest of, `\|h_{k+1,k}\|` and the factor `‖v_{k+1}‖₂`, `1` by (3.1), enter in place of `h_{k+1,k}`, and neither `V_k*V_k = I`, the Hessenberg form nor `‖v‖ = 1` is used; (3.3) prints `V_k^T` for `V_k`, which the statement and its proof do not use | `correct` |
| `Lemma 4.1` | `E(m) - (1 - m)K(m) ∈ (0, 1)` increases, `E'(m) - mK'(m) ∈ (0, 1)` decreases, and (4.3) has a unique `m ∈ (0, 1)` for any `α, β > 0`. | — | — |
| `Eq. 4.5` | `Φ̃ = φ₃∘φ₂∘φ₁` (4.1), (4.2), (4.4) maps the exterior of `[a, b] × [-c, c]` conformally onto the exterior of the unit disk. | n/a — restated from Markushevich [19, p. 178] for `φ₂`; `φ₁`, `φ₃` are a shift and a Möbius map | `restated` |
| `Lemma 4.2` | For `u = x + iy`, `-K < x < K`, `0 < y < 2K'`: `sgn Im cn(u\|m) = sgn Im dn(u\|m)`. | — | — |
| `Lemma 4.3` | The left-most point of `C_r = Ψ̃({\|u\| = r})` is `Ψ̃(-r)`: `min{Re z̃ : z̃ ∈ C_r} = Ψ̃(-r)`. | — | — |
| `Lemma 4.4` | `Ψ̃(-r) = a - 1/λ ∫₀^{(r - 1/r)/2}√(m + t²)/√(1 + t²) dt` (4.23). | — | — |
| `Lemma 4.5` | `lim_{z̃→∞} Φ̃(z̃)/z̃ = 2λ > 0`, `λ` the ratio in (4.3). | — | — |
| `Thm. 5.1` | For upper Hessenberg `H_k` with `a_k`, `b_k`, `c_k` the extreme eigenvalues of its Hermitian part and the largest of its skew-Hermitian part, and `0 < q < 1`: `\|h(t)\| ≤ 2Q q^{k-1}/(1 - q) e^{-tz̃}` (5.2), `Q = 11.08` Crouzeix's constant, `z̃` (5.3). | — | — |
| `Thm. 5.2` | (A priori bound) For `A`, `a`, `b`, `c` of (5.1) and `0 < q < 1`: `‖w(τ) - w_k(τ)‖ ≤ 2Qτ‖A‖ q^{k-1}/(1 - q) e^{-τ min{a,0} - τz̃}` (5.4), `z̃` (5.5). | — partial: [`ErrorLeOfDecayBound.lean`](../../src/CORALean/ContDynamics/LinearSys/Krylov/Theorems/ErrorLeOfDecayBound.lean) proves the last step, from `\|h(s)\| ≤ Ce^{-sz}` and `z ≤ ν(A)` to the error bound `h_{k+1,k}Cτe^{-τz}`, and [`WangYeIntegralStepCounterexample.lean`](../../src/CORALean/ContDynamics/LinearSys/Krylov/Theorems/WangYeIntegralStepCounterexample.lean) the step of the printed proof that fails; missing: (5.2) of `Thm. 5.1`, `Q`, the bounds `h_{k+1,k} ≤ ‖A‖₂` and `z̃ ≤ a`, and (5.4) itself | — |
| `Cor. 5.3` | For `a > 0` (positive definite `A`): `‖w(τ) - w_k(τ)‖ ≤ 2Qτ‖A‖ q^{k-1}/(1 - q) e^{-τ{a - (1/q - q)/(2λ)}}` (5.6), and at `q = 1/(√(a²λ² + 1) + aλ)` the bound `2Qτ‖A‖ q^{k-1}/(1 - q)` (5.7). | — | — |
| `Eq. 5.9` | The minimizing `q = q(k)` of `E(q) = q^{k-1}e^{-τz̃}/(1 - q)` (5.8) solves `(k-1)q + (2-k)q² - C(1 - q)√((1 - q²)² + 4mq²) = 0`, `C = τ/(2λ)`, and has a root in `(0, 1)`. | — | — |
| `Cor. 5.4` | For `m ≈ 0`: `‖w(τ) - w_k(τ)‖ ≤ 2Qτ‖A‖ q₀^{k-1}/(1 - q₀)`, `q₀ = (√κ - 1)/(√κ + 1) + O(√m)`, `κ = b/a`; with the expansions (5.10)-(5.15). | — | — |
| `Eq. 6.4` | (Lanczos, `A = -iH`) With `HV_k = V_kT_k + β_{k+1}v_{k+1}e_k^T` (6.2), `w_k(τ) = V_ke^{iτT_k}e₁` (6.3): `‖w(τ) - w_k(τ)‖ ≤ β_{k+1}∫₀^τ\|h(t)\|dt ≤ ‖H‖∫₀^τ\|h(t)\|dt`, `h(t) = e_k^Te^{itT_k}e₁`. | — partial: [`ErrorLeIntegralDeltaLanczos.lean`](../../src/CORALean/ContDynamics/LinearSys/Krylov/Theorems/ErrorLeIntegralDeltaLanczos.lean) proves the first inequality, for Hermitian `H`, from `Thm. 3.1` with `A = -iH` (so `ν = 0`), `H_k = -iT_k`; missing: the second inequality `β_{k+1} ≤ ‖H‖` | — |
| `Eq. 6.5` | The shifted form: `‖w(τ) - w_k(τ)‖ ≤ ‖H - αI‖∫₀^τ\|h(t)\|dt` for any real `α`. | — | — |
| `Thm. 6.1` | For `A = -iH` skew-Hermitian, `ρ = (λ_max(H) - λ_min(H))/4` and `0 < q < 1`: `‖w(τ) - w_k(τ)‖ ≤ 4 min{1/(1 - q²), τρ/q} q^k/(1 - q) e^{τρ(1/q - q)}` (6.6). | — | — |
| `Eq. 6.8` | The minimizer of `E_s(q) = q^k e^{τρ(1/q - q)}` (6.8) is `q₀ = (k - √(k² - 4(τρ)²))/(2τρ)` for `k > 2τρ` and `E_s` decreases up to `q = 1` for `k ≤ 2τρ`; likewise the root of `τρq⁴ + (3 - k)q³ + q² + kq - τρ = 0` for (6.7). | — | — |
| `Eq. 6.9` | (6.6) with `q = τρ/k` reduces, for `k ≥ 2ρτ`, to Hochbruck and Lubich's `‖w(τ) - w_k(τ)‖ ≤ 12e^{-(ρτ)²/k}(eρτ/k)^k` [18, Thm. 4], the constant being `32/3 ≤ 12`. | — | — |
| `Eq. 7.1` | Saad's bound `‖w(τ) - w_k(τ)‖ ≤ 2(τ‖A‖)^k/k!` for positive semidefinite `A`. | n/a — restated from Saad 1992 [27, Cor. 2.2] | `restated` |
| `Eq. 7.2` | Hochbruck and Lubich's bound `12e^{-ρτ}(eρτ/k)^k` for `k ≥ 2ρτ`, `W(A)` in the disk `\|z - ρ\| < ρ`. | n/a — restated from Hochbruck and Lubich 1997 [18, Thm. 2] | `restated` |
| `Sec. 7` | Examples 1-4, Figures 1-5: the bounds (3.6), (5.4), (6.6) against the error, the Saad and Hochbruck-Lubich bounds, for block diagonal, positive definite and convection-diffusion matrices. | n/a — experiments | `not-a-claim` |
| `Sec. 8` | Concluding remarks. | n/a — discussion | `not-a-claim` |

## Findings

**`Thm. 5.2` — the integration step is wrong for `z̃ > 0`.** The proof integrates (5.2) against
(3.6): `∫₀^τ e^{-tz̃}dt = e^{-τz̃}(e^{τz̃} - 1)/z̃ ≤ τe^{-τz̃}` "where we have used
`(e^x - 1)/x ≤ 1` for any `x ≠ 0`". That inequality holds for `x < 0` only, and `z̃ > 0` is the case
the paper is about (positive definite `A`, Cor. 5.3): at `z̃ = τ = 1`, `∫₀¹e^{-t}dt = 1 - e^{-1} >
e^{-1}`. With (3.6), whose weight is `e^{-min{a,0}τ}`, the proof gives
`2Q‖A‖ q^{k-1}/(1 - q) e^{-τ min{a,0}} min(τ, 1/z̃)`, not the printed (5.4), which is smaller for `z̃ > 0`.
The printed bound is not refuted: integrating (5.2) against the weighted bound of the proof of
`Thm. 3.1` instead, `∫₀^τ e^{(t-τ)a}e^{-tz̃}dt ≤ τe^{-τz̃}` since `z̃ ≤ a` (the integral in (5.5) is
nonnegative), which is (5.4) with `e^{-τ min{a,0}}` dropped. `Cor. 5.3` and (5.6) depend on the same
step. The `Thm. 5.2` row stays `—` while (5.2) is not formalized; the step itself is
[`ErrorLeOfDecayBound.lean`](../../src/CORALean/ContDynamics/LinearSys/Krylov/Theorems/ErrorLeOfDecayBound.lean)
and its failure as printed
[`WangYeIntegralStepCounterexample.lean`](../../src/CORALean/ContDynamics/LinearSys/Krylov/Theorems/WangYeIntegralStepCounterexample.lean).

**Notation of Sec. 3.** (3.3) writes `w_k(τ) = V_k^Te^{-τH_k}e₁`, with the transpose, while `Thm. 3.1`
and the line before (3.3) use `V_ke^{-τH_k}e₁`; `H_k = V_k^TAV_k` and (3.2)'s `h²_{i,k}` are for real
matrices and read `V_k*`, `|h_{i,k}|²` for the complex `A` of the theorem; `e_k ∈ ℝⁿ` is `ℝᵏ`; and
`Thm. 5.1` defines `b_k` with a stray `H_k*^T`. None reaches a statement; the Lean theorems use
`V_k`, the complex conjugate transpose where needed and `e_k ∈ ℂᵏ`.

**`Thm. 3.1` needs no nonexpansive hypothesis.** Unlike `Thm. 1` of
[Jawecki et al.](../2020/jawecki-bit-krylov-error-bounds.md), which holds only for `W(σA) ⊆ ℂ⁻`,
(3.6) holds for every `A`: the cost of `ν(A) < 0` is the factor `e^{-ντ}`, and the weighted form
`∫|h(t)|e^{(t-τ)ν}dt` is the sharper intermediate quantity.

**CORA's `priv_subspace_Krylov_individual_Wang`, which has no caller.** It evaluates
`‖v‖ · h_{K+1,K} · Σ_i |h(iΔ)| e^{(iΔ - t_f)ν} Δ`, `Δ = timeStep`, as the weighted integral of the proof
of `Thm. 3.1`, but with four departures from the theorem, none reachable from `linearSys` methods and
none witnessed in Lean. (1) `arnoldi(A, v, krylovOrder + 1)` returns `V`, `H` of dimension `K = krylovOrder + 1`
and `Hlast = h_{K+1,K}`, while the sum reads the `(krylovOrder, 1)` entry of `e^{-tH}`, that is `e_k*e^{-tH_K}e₁`
for `k = K - 1`, not the `(K, 1)` entry `h(t)` of `Thm. 3.1` for `H_K`. The bound is then not
that of the theorem, and in a replication in Python of the routine's arithmetic (random real matrices,
`n ∈ {4, ..., 7}`, `Δ = t_f/100`, `ν = λ_min` of the Hermitian part) it fell below the actual error of the returned
order in 3 of 2848 cases (for example `n = 5`, `krylovOrder = 1`, `t_f = 1`: `0.867` against `1.080`), while the `(K, 1)` entry never did (not
run in MATLAB). (2) `expm(-t*H)` and `nu_A` follow the paper's `e^{-τA}`, so a caller would pass `-A` of
`ẋ = Ax`; `nu_A` is documented as the "minimum eigenvalue of `A`", while `ν(A)` is the least eigenvalue of
the Hermitian part, which for a non-normal `A` can be smaller than the least real part of the
spectrum, and a `nu_A` above `ν(A)` makes the weight `e^{(t-τ)ν}` too small for the theorem. (3) The sum is the right-endpoint Riemann sum of
the integral over the `ceil(t_f/Δ)` points `iΔ`, an approximation, not an upper bound (the
paper remarks the integral is "not directly computable" and approximates it by Simpson's rule); and
the last point exceeds `t_f` unless `Δ` divides `t_f`. (4) The Arnoldi vectors are computed in floating
point (`(2.2)`'s orthogonality holds to rounding) and the breakdown test `H(j+1,j) <= eps` is absolute.
