# Computable upper error bounds for Krylov approximations to matrix exponentials and associated φ-functions

T. Jawecki, W. Auzinger, O. Koch. "Computable upper error bounds for Krylov approximations to matrix exponentials and associated φ-functions". BIT Numerical Mathematics, 60(1):157-197, 2020.

**Source:** https://arxiv.org/pdf/1809.03369 (arXiv:1809.03369v2, 11 Feb 2019, the authors' version, 26 pages, read in full; text extracted with `pypdf`). The typeset BIT article (doi:10.1007/s10543-019-00771-6, published online 11 Sep 2019) was not reachable; numbering is the arXiv version's. CORA's `linearSys/private/priv_subspace_Krylov_individual_Jawecki.m` cites "equation 3.6 of [1]" and "(Err_a) in [1]", and `priv_subspace_Krylov_jaweckiBound.m` the paper without a result number.  
**Inventory:** confirmed (Propositions 1-6, Theorems 1-3, Remarks 1-8, equations (2.1)-(7.9) and (8.1)-(8.3), Tables 8.1-8.4, Figures 8.1-8.7; no Definitions, Lemmas, Corollaries or Algorithms; the rows below are the results and the numbered displays that make a claim)

A computable a-posteriori bound for the standard Krylov approximation `V_m e^{σtT_m}e₁` of
`e^{σtA}v`: in the nonexpansive case `W(σA) ⊆ ℂ⁻` the error is at most
`τ_{m+1,m} γ_m t^m/m!` (`Thm. 1`, Err_a), `γ_m` the product of the subdiagonal of `T_m`. CORA's
`linearSys` Krylov reachability (`priv_initReach_Krylov`, through
`priv_subspace_Krylov_jaweckiBound`, `priv_inputSolution_Krylov` and `priv_krylov_R_uTrans`)
chooses its Krylov orders by Err_a. Formalized: the Hessenberg identities (2.3)-(2.5), the
defect (2.9), the field-of-values inclusions (3.4), the accumulated error of restarted steps
((7.2), `Sec. 7`) and mass conservation (8.3), over any commutative ring or over ℂ. `Thm. 1` itself is not: its `Prop. 2` bounds a divided
difference over the complex spectrum of `T_m`. CORA evaluates Err_a without the nonexpansive
hypothesis, where it is no bound (Findings).

## Results

| Result | What it says | In CORALean | Class |
|---|---|---|---|
| `Eq. 2.2` | (Krylov identity) The Arnoldi iteration gives `V_m ∈ ℂ^{n×m}`, `V_m*V_m = I`, and an upper Hessenberg `T_m` with `AV_m = V_mT_m + τ_{m+1,m}v_{m+1}e_m*`, `τ_{m+1,m} ∈ ℝ₊`, `‖v_{m+1}‖₂ = 1`. | n/a — restated from Saad's book [43]; the real Arnoldi relation is `Alg. 1` on [Althoff 2020](althoff-tac-krylov.md) | `restated` |
| `Remark 1` | Run to dimension `m`, Arnoldi gives positive subdiagonal entries of `T_m`; a breakdown is lucky, the approximation of the step before being exact. | n/a — restated from Saad 1992 [42] | `restated` |
| `Eq. 2.3` | `e_m*T_mʲe₁ = 0` for `j = 0, …, m - 2`, by the upper Hessenberg structure of `T_m`. | [`HessenbergPowApplyEqZero.lean`](../../src/CORALean/ContDynamics/LinearSys/Krylov/Theorems/HessenbergPowApplyEqZero.lean) — over any semiring, `(T_mʲ)_{i,l} = 0` for `i > l + j`. **As printed:** row `m`, column `1` is `m > 1 + j`, that is `j ≤ m - 2` | `correct` |
| `Eq. 2.4` | `Aʲv = V_mT_mʲe₁` for `0 ≤ j ≤ m - 1`, from (2.2) and the Hessenberg structure. | [`PowMulVecOfKrylovIdentity.lean`](../../src/CORALean/ContDynamics/LinearSys/Krylov/Theorems/PowMulVecOfKrylovIdentity.lean) — from (2.2) and (2.3), `v = V_me₁`, over any commutative ring | `correct` |
| `Eq. 2.5` | `γ_m = e_m*T_m^{m-1}e₁ = ∏_{j=1}^{m-1}(T_m)_{j+1,j}`. | [`HessenbergPowApplyLastEqProd.lean`](../../src/CORALean/ContDynamics/LinearSys/Krylov/Theorems/HessenbergPowApplyLastEqProd.lean) — over any commutative semiring | `correct` |
| `Eq. 2.8` | (Defect-based error representation) `L_m(t)v = ∫₀ᵗ E(t - s)D_m(s)v ds`, from `L_m'(t)v = σAL_m(t)v + D_m(t)v`, `L_m(0)v = 0`. | — | — |
| `Eq. 2.9` | `D_m(s)v = σAV_me^{σsT_m}e₁ - σV_mT_me^{σsT_m}e₁ = σ(AV_m - V_mT_m)e^{σsT_m}e₁ = στ_{m+1,m}(e_m*e^{σsT_m}e₁)v_{m+1}`. | [`DefectOfKrylovIdentity.lean`](../../src/CORALean/ContDynamics/LinearSys/Krylov/Theorems/DefectOfKrylovIdentity.lean) — from (2.2), over any commutative ring, for every vector in place of `e^{σsT_m}e₁`. **As printed:** the display's first expression is `D_m(s)v = σAS_m(s)v - S_m'(s)v` with Mathlib's derivative of the exponential (`hasDerivAt_exp_smul_const`), and its equalities are the theorem at `y = e^{σsT_m}e₁` | `correct` |
| `Eq. 2.10` | `D_m(t)v = στ_{m+1,m}γ_m(σt)^{m-1}/(m-1)! v_{m+1} + O(t^m)` as `t → 0`, hence `‖D_m(t)v‖ = O(t^{m-1})` and `‖L_m(t)v‖ = O(t^m)` (2.11). | — | — |
| `Prop. 1` | For any `A`, `L_m(t)v = τ_{m+1,m}γ_m(σt)^m/m! v_{m+1} + R_{m+1}(t)`, `R_{m+1}(t) = O(t^{m+1})` (2.12). | — | — |
| `Remark 2` | `R_{m+1}(t) = (σt)^{m+1}/m! ∫₀¹(A^{m+1}e^{σθtA}v - V_mT_m^{m+1}e^{σθtT_m}e₁)(1 - θ)^m dθ`. | — | — |
| `Eq. 3.1b` | (Nonexpansive case) `‖L_m(t)v‖₂ ≤ τ_{m+1,m}∫₀ᵗ\|δ_m(s)\|ds`, `δ_m(s) = e_m*e^{σsT_m}e₁` (3.1a). | — | — |
| `Eq. 3.4` | `spec(σT_m) ⊆ W(σT_m) ⊆ W(σA) ⊆ ℂ⁻`. | [`SpectrumSubsetOfKrylovIdentity.lean`](../../src/CORALean/ContDynamics/LinearSys/Krylov/Theorems/SpectrumSubsetOfKrylovIdentity.lean) — from (2.2) with `V_m*V_m = I` and `V_m*v_{m+1} = 0`, through `T_m = V_m*AV_m`; the last inclusion is the nonexpansive hypothesis, and with it `spec(σT_m) ⊆ ℂ⁻`. **As printed:** `W(M)` is written as the set of Rayleigh quotients `x*Mx/x*x`, `x ≠ 0`, the same set as `{x*Mx : ‖x‖₂ = 1}`, and `V_m*v_{m+1} = 0` is part of the orthonormal Arnoldi basis (2.2) is built from | `correct` |
| `Prop. 2` | For upper Hessenberg `T_m` with eigenvalues `λ₁, …, λ_m` and `spec(σT_m) ⊆ ℂ⁻`: `δ_m(t) = f_t[λ₁, …, λ_m]γ_m ≤ t^{m-1}/(m-1)! γ_m` (3.5), `f_t(λ) = e^{σtλ}` (3.3) and `f_t[…]` its `(m-1)`-th divided difference. | — | — |
| `Thm. 1` | (Computable upper bound) In the nonexpansive case `‖L_m(t)v‖₂ ≤ τ_{m+1,m}γ_m t^m/m!` (3.6), Err_a. | — partial: [`Krylov.hessenberg_pow_apply_last_eq_prod`](../../src/CORALean/ContDynamics/LinearSys/Krylov/Theorems/HessenbergPowApplyLastEqProd.lean), [`Krylov.defect_of_krylovIdentity`](../../src/CORALean/ContDynamics/LinearSys/Krylov/Theorems/DefectOfKrylovIdentity.lean); missing: (2.8), (3.1b) and `Prop. 2`'s bound on `\|δ_m(s)\|` | — |
| `Prop. 3` | (Asymptotical correctness) `‖L_m(t)v‖₂ = τ_{m+1,m}γ_m t^m/m! + O(t^{m+1})` (3.7). | — | — |
| `Remark 3` | The results do not carry over directly to shift-and-invert Krylov approximations. | n/a — a remark on scope | `not-a-claim` |
| `Eq. 4.1` | `φ_p(z) = Σ_k z^k/(k + p)!` (4.1a), `φ₀(z) = e^z`, and `φ_p(z) = 1/(p-1)! ∫₀¹(1 - θ)^{p-1}e^{θz}dθ` for `p ≥ 1` (4.1b). | — | — |
| `Thm. 2` | `L^p_m(t)v = τ_{m+1,m}γ_m(σt)^m/(m + p)! v_{m+1} + O(t^{m+1})` (4.4a), and in the nonexpansive case `‖L^p_m(t)v‖₂ ≤ τ_{m+1,m}γ_m t^m/(m + p)!` (4.4b), asymptotically correct. | — | — |
| `Prop. 4` | `L_m(t)v = τ_{m+1,m}σt Σ_{j≥1} e_m*φ_j(σtT_m)e₁ (σtA)^{j-1}v_{m+1}` (5.1). | n/a — restated from Saad 1992 [42, Thm. 5.1] | `restated` |
| `Eq. 5.2` | `e^{σtT⁺_m}e₁ = [e^{σtT_m}e₁; τ_{m+1,m}σt(e_m*φ₁(σtT_m)e₁)]` for the extended matrix `T⁺_m` (5.2a). | n/a — restated from Saad 1992 [42, Prop. 2.1] | `restated` |
| `Prop. 5` | The error series (5.5a) of `L^p_m(t)v` and (5.5b) of the corrected `L^{p,+}_m(t)v`. | n/a — restated from Sidje's Expokit paper [44, Thm. 2] | `restated` |
| `Remark 4` | `e_m*φ_j(σtT_m)e₁ = γ_m(σt)^{m-1}/(m - 1 + j)! + O(t^m)` (5.6), the leading terms (5.7a), (5.7b) and the estimators Err₁ (5.8a), (5.8b). | — | — |
| `Thm. 3` | `L^{p,+}_m(t)v = τ_{m+1,m}γ_m(σt)^{m+1}/(m + p + 1)! Av_{m+1} + O(t^{m+2})` (5.9a), and in the nonexpansive case `‖L^{p,+}_m(t)v‖₂ ≤ ‖Av_{m+1}‖₂τ_{m+1,m}γ_m t^{m+1}/(m + p + 1)!` (5.9b), asymptotically correct. | — | — |
| `Prop. 6` | Nonexpansive, `σ = 1`, `A` Hermitian: `\|δ_m(t)\| = δ_m(t) > 0` for `t > 0`, `‖L^p_m(t)v‖₂ ≤ τ_{m+1,m}t e_m*φ_{p+1}(tT_m)e₁` (5.10a) and `‖L^{p,+}_m(t)v‖₂ ≤ ‖Av_{m+1}‖₂τ_{m+1,m}t² e_m*φ_{p+2}(tT_m)e₁` (5.10b). | — | — |
| `Sec. 6` | The Hermite quadrature (6.2), the estimate (6.3) and the trapezoidal estimate (6.6) of the error integral. | n/a — approximations, not bounds | `not-a-claim` |
| `Eq. 6.4` | (Peano representation) `t/m Θ_m(t, t) - ∫₀ᵗΘ_m(s, t)v ds = ∫₀ᵗ s(t - s)^{m-1}/m! ∂^m_sΘ_m(s, t)v ds`, so the quadrature error is `O(t^{m+1})`. | — | — |
| `Eq. 6.5` | `∫₀ᵗΘ_m(s, t)v ds = 2t/(m + 1) D_m(t)v - t²/(m(m + 1)) D^{[2]}_m(t)v + O(t^{m+2})`, and the longer expansion after it. | — | — |
| `Eq. 6.8` | With `f(t) = \|δ_m(t)\| > 0` on `(0, T]` and its effective order `1 ≤ m̃ ≤ ρ(t) ≤ m - 1`: `t/m \|δ_m(t)\| ≤ ∫₀ᵗ\|δ_m(s)\|ds ≤ t/(m̃ + 1)\|δ_m(t)\| ≤ t/2 \|δ_m(t)\|`. | — | — |
| `Remark 5` | The effective order quadrature estimate (6.9). | n/a — a heuristic choice of `m̃` | `not-a-claim` |
| `Eq. 7.1` | Superlinear convergence sets in for `t‖A‖₂ ⪅ m`, recalled from [23]. | n/a — a rough estimate, as the paper says | `not-a-claim` |
| `Eq. 7.2` | (Accumulated error of restarted steps) `L⋆_m(t)v = v^{[N]} - w^{[N]} = Σ_{j=1}^N E(Δt_N)⋯E(Δt_{j+1})L^{[j]}_m(Δt_j)w^{[j-1]}`. | [`RestartedErrorEqSum.lean`](../../src/CORALean/ContDynamics/LinearSys/Krylov/Theorems/RestartedErrorEqSum.lean) — for additive `E_j` and any `S_j` on an additive group, steps counted from `0` | `correct` |
| `Sec. 7` | With `E(·)` nonexpansive and the local error bounded by `‖L^{[j]}_m(Δt_j)w^{[j]}‖₂ ≤ tol · Δt_j` (7.3): `‖L⋆_m(t)v‖₂ ≤ Σ_j‖L^{[j]}_m(Δt_j)w^{[j-1]}‖₂ ≤ tol · t`. | [`RestartedErrorLe.lean`](../../src/CORALean/ContDynamics/LinearSys/Krylov/Theorems/RestartedErrorLe.lean) — for additive `E_j` that do not increase the norm, any `S_j`, any normed group, with (7.3) at `w^{[j-1]}` | `underspecified` — (7.3) bounds `L^{[j]}_m(Δt_j)w^{[j]}`, while the sum it is applied to, and the local error of the `j`-th step, is `L^{[j]}_m(Δt_j)w^{[j-1]}`; see Findings |
| `Eq. 7.4` | Step sizes from Err_a: `Δt_j = (tol m!/(τ^{[j]}_{m+1,m}γ^{[j]}_m))^{1/m}` (7.4), with `tol · Δt_j` (7.5), and from (5.9b) (7.6). | n/a — step-size choices | `not-a-claim` |
| `Eq. 7.7` | The heuristic step size control (7.7), Expokit's first step (7.8) and the iteration (7.9) of `Remark 6`. | n/a — heuristics | `not-a-claim` |
| `Remark 6` | For Hermitian `A`, the eigenvalue decomposition of `T_m` makes Err₁ cheap for many `Δt`, iterated by (7.9). | n/a — a remark on cost | `not-a-claim` |
| `Eq. 8.3` | (Mass conservation) For `σ = -i`, Hermitian `A`, `‖v‖₂ = 1` and `V_m*V_m = I`: `‖S_m(t)v‖₂ = ‖V_me^{-itT_m}e₁‖₂ = e₁*e^{itT_m}V_m*V_me^{-itT_m}e₁ = 1`. | [`KrylovApproxMassConserved.lean`](../../src/CORALean/ContDynamics/LinearSys/Krylov/Theorems/KrylovApproxMassConserved.lean) — `y*y = 1` for `y = V_me^{-itT_m}e₁`, `T_m` Hermitian. **As printed:** `‖y‖₂ = 1` is `y*y = 1`, which is also the printed middle term; `T_m = V_m*AV_m` is Hermitian for Hermitian `A` | `correct` |
| `Sec. 8` | The free Schrödinger, Hubbard, heat and convection-diffusion experiments, `Remark 7` and `Remark 8` (Tables 8.1-8.4, Figs. 8.1-8.7). | n/a — experiments | `not-a-claim` |

## Findings

**`Sec. 7` — the start vector of the local error.** The accumulated error is
`v^{[j]} - w^{[j]} = E(Δt_j)(v^{[j-1]} - w^{[j-1]}) + L^{[j]}_m(Δt_j)w^{[j-1]}`, and the bound
sums `‖L^{[j]}_m(Δt_j)w^{[j-1]}‖₂`, the error of the `j`-th Krylov step at the vector it starts
from, whose Krylov space builds `V^{[j]}_m`. The assumption (7.3) bounds
`‖L^{[j]}_m(Δt_j)w^{[j]}‖₂` instead, and the text after it calls that term "the truncation error
of a single substep" again. Read with `w^{[j-1]}`, the bound holds for any nonexpansive steps
and any approximations `S^{[j]}_m`.
[`RestartedErrorLe.lean`](../../src/CORALean/ContDynamics/LinearSys/Krylov/Theorems/RestartedErrorLe.lean)

**`Prop. 2` — a complex number bounded by a real one.** (3.5) reads
`δ_m(t) = f_t[λ₁, …, λ_m]γ_m ≤ t^{m-1}/(m-1)! γ_m`, but `δ_m(t)` is complex for complex `σ` or
`T_m`; the proof bounds `|f_t[λ₁, …, λ_m]|`, and `Thm. 1` uses `|δ_m(s)| ≤ s^{m-1}/(m-1)! γ_m`.
The row stays `—` until `Prop. 2` is formalized.

**CORA's use of `Thm. 1`, outside the nonexpansive case.** Err_a is a bound only when
`W(σA) ⊆ ℂ⁻`; the proof needs `‖E(t - s)‖₂ ≤ 1` in (3.1b) and `spec(σT_m) ⊆ ℂ⁻` in `Prop. 2`.
`priv_subspace_Krylov_individual_Jawecki` computes `errorBound = τ γ tFinal^m/m!` (with
`tau = Hlast` and `gamma` the product of `H(i+1,i)`, as (2.5)) for whatever matrix it is
handed and accepts the order once `‖v‖ · errorBound ≤ krylovError`; nothing in
`linearSys/reach` with `linAlg = 'krylov'` checks `A`, and the error box CORA adds is
`krylovError`. `priv_inputSolution_Krylov` and `priv_krylov_R_uTrans` hand it the integrator
matrix `C̃ = [A u; 0 0]`, whose field of values is never in `ℂ⁻` for `u ≠ 0` (at `x = (εu, 1)`,
`x*C̃x = ε²u*Au + ε‖u‖²` is positive for small `ε > 0`), at the start vector `[0ₙ; 1]` and order
`1 + krylovStep ≥ 2`. For `A = [0 0; 1 1]` (`e₂*Ae₂ = 1`), `u = e₁`, Arnoldi gives
`V = [e₃ e₁]`, `τ₃,₂ = γ₂ = 1`, so Err_a at order `2` is `t²/2`, while the second coordinate of
`e^{tC̃}e₃`, which `V` cannot reach, is `e^t - 1 - t > t²/2` for every `t > 0`: with
`tFinal = timeStep = t` and `krylovError = t²/2` CORA accepts order `2`, and the box of radius
`krylovError` that `priv_krylov_R_uTrans` puts around `V e^{tT}e₁` misses the solution for the
constant input `u` (read from the source, not run). On the integrator matrix of a nonexpansive `A`
the bound does hold — the error integrand there is `E(t - s)` at `[w; 0]`, on which `C̃` acts as
`A`, and `T_m`'s first row vanishes, so its spectrum is `0` and that of a compression of `A` —
argued, not formalized. Two further departures from the paper's setting are not witnessed: the
Arnoldi vectors are computed in floating point, so (2.2) and `V_m*V_m = I` hold only to rounding
(the paper's Table 8.1 shows the loss of orthogonality), and the happy breakdown test is
`H(j+1,j) <= eps`, absolute rather than relative to `‖A‖`.
[`JaweckiBoundCoraCounterexample.lean`](../../src/CORALean/ContDynamics/LinearSys/Krylov/Theorems/JaweckiBoundCoraCounterexample.lean)
