# Computable upper error bounds for Krylov approximations to matrix exponentials and associated φ-functions

```bibtex
@article{jawecki2020computable,
  author = {Jawecki, T. and Auzinger, W. and Koch, O.},
  title = {Computable upper error bounds for {Krylov} approximations to matrix exponentials and associated φ-functions},
  journal = {BIT Numerical Mathematics},
  year = {2020}
}
```

**Source:** https://arxiv.org/pdf/1809.03369 (arXiv:1809.03369v2, 11 Feb 2019, the authors' version, 26 pages, read in full; text extracted with `pypdf`). The typeset BIT article (doi:10.1007/s10543-019-00771-6, published online 11 Sep 2019) was not reachable; numbering is the arXiv version's. CORA's `linearSys/private/priv_subspace_Krylov_individual_Jawecki.m` cites "equation 3.6 of [1]" and "(Err_a) in [1]", and `priv_subspace_Krylov_jaweckiBound.m` the paper without a result number.  
**Inventory:** confirmed (Propositions 1-6, Theorems 1-3, Remarks 1-8, equations (2.1)-(7.9) and (8.1)-(8.3), Tables 8.1-8.4, Figures 8.1-8.7; no Definitions, Lemmas, Corollaries or Algorithms; the rows below are the results and the numbered displays that make a claim)

A computable a-posteriori bound for the standard Krylov approximation `V_m e^{σtT_m}e₁` of
`e^{σtA}v`: in the nonexpansive case `W(σA) ⊆ ℂ⁻` the error is at most
`τ_{m+1,m} γ_m t^m/m!` (`Thm. 1`, Err_a), `γ_m` the product of the subdiagonal of `T_m`. CORA's
`linearSys` Krylov reachability (`priv_initReach_Krylov`, through
`priv_subspace_Krylov_jaweckiBound`, `priv_inputSolution_Krylov` and `priv_krylov_R_uTrans`)
chooses its Krylov orders by Err_a. Formalized: the Hessenberg identities (2.3)-(2.5), the
defect (2.9), the field-of-values inclusions (3.4), the accumulated error of restarted steps
((7.2), `Sec. 7`) and mass conservation (8.3), over any commutative ring or over ℂ. Also formalized: `Thm. 1` itself with the paper's hypotheses, through the error integral (2.8), its bound (3.1b) and
`Prop. 2`'s estimate of `|δ_m|`, proved under `W(σT_m) ⊆ ℂ⁻` by induction on `m` rather than through divided differences. Further: the asymptotics (2.10)-(2.12) and (3.7) of `Prop. 1` and
`Prop. 3`, the explicit remainder of `Remark 2`, the leading terms of `Remark 4`, the φ-function
representation (4.1), Err_a for φ-functions (`Thm. 2`) and for the corrected approximation
(`Thm. 3`, through a Krylov identity of one dimension more rather than the restated `Prop. 5`),
and the effective-order bounds (6.8).
CORA evaluates Err_a without the nonexpansive hypothesis, where it is no bound (Findings).

## Results

| Result | What it says | In CORALean | Class |
|---|---|---|---|
| `Eq. 2.2` | (Krylov identity) The Arnoldi iteration gives `V_m ∈ ℂ^{n×m}`, `V_m*V_m = I`, and an upper Hessenberg `T_m` with `AV_m = V_mT_m + τ_{m+1,m}v_{m+1}e_m*`, `τ_{m+1,m} ∈ ℝ₊`, `‖v_{m+1}‖₂ = 1`. | n/a — restated from Saad's book [43]; the real Arnoldi relation is `Alg. 1` on [Althoff 2020](althoff-tac-krylov.md) | `restated` |
| `Remark 1` | Run to dimension `m`, Arnoldi gives positive subdiagonal entries of `T_m`; a breakdown is lucky, the approximation of the step before being exact. | n/a — restated from Saad 1992 [42] | `restated` |
| `Eq. 2.3` | `e_m*T_mʲe₁ = 0` for `j = 0, …, m - 2`, by the upper Hessenberg structure of `T_m`. | [`HessenbergPowApplyEqZero.lean`](../../src/CORALean/ContDynamics/LinearSys/Krylov/Theorems/HessenbergPowApplyEqZero.lean) — over any semiring, `(T_mʲ)_{i,l} = 0` for `i > l + j`. **As printed:** row `m`, column `1` is `m > 1 + j`, that is `j ≤ m - 2` | `correct` |
| `Eq. 2.4` | `Aʲv = V_mT_mʲe₁` for `0 ≤ j ≤ m - 1`, from (2.2) and the Hessenberg structure. | [`PowMulVecOfKrylovIdentity.lean`](../../src/CORALean/ContDynamics/LinearSys/Krylov/Theorems/PowMulVecOfKrylovIdentity.lean) — from (2.2) and (2.3), `v = V_me₁`, over any commutative ring | `correct` |
| `Eq. 2.5` | `γ_m = e_m*T_m^{m-1}e₁ = ∏_{j=1}^{m-1}(T_m)_{j+1,j}`. | [`HessenbergPowApplyLastEqProd.lean`](../../src/CORALean/ContDynamics/LinearSys/Krylov/Theorems/HessenbergPowApplyLastEqProd.lean) — over any commutative semiring | `correct` |
| `Eq. 2.8` | (Defect-based error representation) `L_m(t)v = ∫₀ᵗ E(t - s)D_m(s)v ds`, from `L_m'(t)v = σAL_m(t)v + D_m(t)v`, `L_m(0)v = 0`. | [`ErrorEqIntegralDefect.lean`](../../src/CORALean/ContDynamics/LinearSys/Krylov/Theorems/ErrorEqIntegralDefect.lean) — for any `y` with `y' = My + D`, `y(0) = 0` and continuous `D`, `M = σA`, `E(t) = e^{tM}`; [1]'s `D_m(s)v` (2.9) is continuous in `s` | `correct` |
| `Eq. 2.9` | `D_m(s)v = σAV_me^{σsT_m}e₁ - σV_mT_me^{σsT_m}e₁ = σ(AV_m - V_mT_m)e^{σsT_m}e₁ = στ_{m+1,m}(e_m*e^{σsT_m}e₁)v_{m+1}`. | [`DefectOfKrylovIdentity.lean`](../../src/CORALean/ContDynamics/LinearSys/Krylov/Theorems/DefectOfKrylovIdentity.lean) — from (2.2), over any commutative ring, for every vector in place of `e^{σsT_m}e₁`. **As printed:** the display's first expression is `D_m(s)v = σAS_m(s)v - S_m'(s)v` with Mathlib's derivative of the exponential (`hasDerivAt_exp_smul_const`), and its equalities are the theorem at `y = e^{σsT_m}e₁` | `correct` |
| `Eq. 2.10` | `D_m(t)v = στ_{m+1,m}γ_m(σt)^{m-1}/(m-1)! v_{m+1} + O(t^m)` as `t → 0`, hence `‖D_m(t)v‖ = O(t^{m-1})` and `‖L_m(t)v‖ = O(t^m)` (2.11). | [`DefectSubLeadingIsBigO.lean`](../../src/CORALean/ContDynamics/LinearSys/Krylov/Theorems/DefectSubLeadingIsBigO.lean) — under (2.2), upper Hessenberg `T_m` and `v = V_me₁`, through the Taylor expansion of `e^{tN}x` ([`ExpSmulMulVecTaylorIsBigO.lean`](../../src/CORALean/ContDynamics/LinearSys/Krylov/Theorems/ExpSmulMulVecTaylorIsBigO.lean)), (2.3), (2.5) and (2.9). **As printed:** `O(·)` in the sup norm of `ℂⁿ`, the same in any norm; `‖L_m(t)v‖ = O(t^m)` is read off `Prop. 1` rather than (2.8) | `correct` |
| `Prop. 1` | For any `A`, `L_m(t)v = τ_{m+1,m}γ_m(σt)^m/m! v_{m+1} + R_{m+1}(t)`, `R_{m+1}(t) = O(t^{m+1})` (2.12). | [`ErrorSubLeadingIsBigO.lean`](../../src/CORALean/ContDynamics/LinearSys/Krylov/Theorems/ErrorSubLeadingIsBigO.lean) — any `A`, under (2.2), upper Hessenberg `T_m` and `v = V_me₁`, by the Taylor expansions, (2.4) and (2.5), as in [1]. **As printed:** `O(·)` in the sup norm of `ℂⁿ`, the same in any norm | `correct` |
| `Remark 2` | `R_{m+1}(t) = (σt)^{m+1}/m! ∫₀¹(A^{m+1}e^{σθtA}v - V_mT_m^{m+1}e^{σθtT_m}e₁)(1 - θ)^m dθ`. | [`ErrorRemainderEqIntegral.lean`](../../src/CORALean/ContDynamics/LinearSys/Krylov/Theorems/ErrorRemainderEqIntegral.lean) — `R_{m+1}(t)` the remainder of (2.12), any `A`, under (2.2), upper Hessenberg `T_m` and `v = V_me₁`; the exponential series split after `m + 1` terms ([`ExpEqSumAddPhiMul.lean`](../../src/CORALean/ContDynamics/LinearSys/Krylov/Theorems/ExpEqSumAddPhiMul.lean)) and (4.1b) | `correct` |
| `Eq. 3.1b` | (Nonexpansive case) `‖L_m(t)v‖₂ ≤ τ_{m+1,m}∫₀ᵗ\|δ_m(s)\|ds`, `δ_m(s) = e_m*e^{σsT_m}e₁` (3.1a). | [`ErrorLeIntegralDelta.lean`](../../src/CORALean/ContDynamics/LinearSys/Krylov/Theorems/ErrorLeIntegralDelta.lean) — from (2.2), `v = V_me₁`, `\|σ\| = 1`, through (2.8), (2.9) and `‖E(t - s)‖₂ ≤ 1` ([`NormExpSmulMulVecLe.lean`](../../src/CORALean/ContDynamics/LinearSys/Krylov/Theorems/NormExpSmulMulVecLe.lean)); `V_m*V_m = I` is not needed. **As printed:** `W(σA) ⊆ ℂ⁻` is `Re(x*σAx) ≤ 0` for all `x`, the same condition, `‖·‖₂` the norm of `EuclideanSpace ℂ (Fin n)`, `τ_{m+1,m} ∈ ℝ₊` enters as `\|τ_{m+1,m}\|`, and the bound carries the factor `‖v_{m+1}‖₂`, `1` by (2.2) | `correct` |
| `Eq. 3.4` | `spec(σT_m) ⊆ W(σT_m) ⊆ W(σA) ⊆ ℂ⁻`. | [`SpectrumSubsetOfKrylovIdentity.lean`](../../src/CORALean/ContDynamics/LinearSys/Krylov/Theorems/SpectrumSubsetOfKrylovIdentity.lean) — from (2.2) with `V_m*V_m = I` and `V_m*v_{m+1} = 0`, through `T_m = V_m*AV_m`; the last inclusion is the nonexpansive hypothesis, and with it `spec(σT_m) ⊆ ℂ⁻`. **As printed:** `W(M)` is written as the set of Rayleigh quotients `x*Mx/x*x`, `x ≠ 0`, the same set as `{x*Mx : ‖x‖₂ = 1}`, and `V_m*v_{m+1} = 0` is part of the orthonormal Arnoldi basis (2.2) is built from | `correct` |
| `Prop. 2` | For upper Hessenberg `T_m` with eigenvalues `λ₁, …, λ_m` and `spec(σT_m) ⊆ ℂ⁻`: `δ_m(t) = f_t[λ₁, …, λ_m]γ_m ≤ t^{m-1}/(m-1)! γ_m` (3.5), `f_t(λ) = e^{σtλ}` (3.3) and `f_t[…]` its `(m-1)`-th divided difference. | — partial: [`NormExpApplyLastLe.lean`](../../src/CORALean/ContDynamics/LinearSys/Krylov/Theorems/NormExpApplyLastLe.lean) proves `\|δ_m(t)\| ≤ \|γ_m\| t^{m-1}/(m-1)!` under the stronger `W(σT_m) ⊆ ℂ⁻` (what `Thm. 1` has, by (3.4)), by induction on `m` through (3.1b) for the leading block, without divided differences; missing: the divided-difference identity and the bound under `spec(σT_m) ⊆ ℂ⁻` alone | — |
| `Thm. 1` | (Computable upper bound) In the nonexpansive case `‖L_m(t)v‖₂ ≤ τ_{m+1,m}γ_m t^m/m!` (3.6), Err_a. | [`ErrorLeErrA.lean`](../../src/CORALean/ContDynamics/LinearSys/Krylov/Theorems/ErrorLeErrA.lean) — for `t ≥ 0`, `W(σA) ⊆ ℂ⁻` (as `Re(x*σAx) ≤ 0`), `\|σ\| = 1`, (2.2) with `[V_m v_{m+1}]` orthonormal, `τ_{m+1,m} ≥ 0`, `‖v_{m+1}‖₂ = 1`, upper Hessenberg `T_m` and `v = V_me₁`, through (3.1b), (3.4) and `Prop. 2`'s estimate under `W(σT_m) ⊆ ℂ⁻`. **As printed:** `γ_m` enters as `\|γ_m\|`, equal to `γ_m` for Arnoldi's positive subdiagonal (`Remark 1`); the bound uses `\|δ_m(s)\|`, so the misprint in (3.5) does not reach it. Without the nonexpansive hypothesis it fails ([`JaweckiBoundCora.lean`](../../src/CORALean/ContDynamics/LinearSys/Krylov/Counterexamples/JaweckiBoundCora.lean)) | `correct` |
| `Prop. 3` | (Asymptotical correctness) `‖L_m(t)v‖₂ = τ_{m+1,m}γ_m t^m/m! + O(t^{m+1})` (3.7). | [`NormErrorSubErrAIsBigO.lean`](../../src/CORALean/ContDynamics/LinearSys/Krylov/Theorems/NormErrorSubErrAIsBigO.lean) — any `A`, under (2.2) with `τ_{m+1,m} ≥ 0`, `‖v_{m+1}‖₂ = 1`, `\|σ\| = 1`, upper Hessenberg `T_m`, `v = V_me₁`, from `Prop. 1` by the reverse triangle inequality, as in [1]. **As printed:** `t → 0` is `t → 0⁺`, `t` being a step size (at `t < 0` the leading norm is `\|t\|^m`), and `γ_m` enters as `\|γ_m\|`, `γ_m` for Arnoldi's positive subdiagonal | `correct` |
| `Remark 3` | The results do not carry over directly to shift-and-invert Krylov approximations. | n/a — a remark on scope | `not-a-claim` |
| `Eq. 4.1` | `φ_p(z) = Σ_k z^k/(k + p)!` (4.1a), `φ₀(z) = e^z`, and `φ_p(z) = 1/(p-1)! ∫₀¹(1 - θ)^{p-1}e^{θz}dθ` for `p ≥ 1` (4.1b). | [`PhiSeriesEqIntegral.lean`](../../src/CORALean/ContDynamics/LinearSys/Krylov/Theorems/PhiSeriesEqIntegral.lean) — for `z` in any complete normed ℝ-algebra, so for complex `z` and for the matrices of (4.2), through the Beta integral ([`IntegralOneSubPowMulPow.lean`](../../src/CORALean/ContDynamics/LinearSys/Krylov/Theorems/IntegralOneSubPowMulPow.lean)). **As printed:** (4.1a) is the definition, `p ≥ 1` is written `p + 1` | `correct` |
| `Thm. 2` | `L^p_m(t)v = τ_{m+1,m}γ_m(σt)^m/(m + p)! v_{m+1} + O(t^{m+1})` (4.4a), and in the nonexpansive case `‖L^p_m(t)v‖₂ ≤ τ_{m+1,m}γ_m t^m/(m + p)!` (4.4b), asymptotically correct. | [`PhiErrorLeErrA.lean`](../../src/CORALean/ContDynamics/LinearSys/Krylov/Theorems/PhiErrorLeErrA.lean) — `φ_p` the series (4.1a), in the setting of `Thm. 1`; (4.4b) under `W(σA) ⊆ ℂ⁻` (as `Re(x*σAx) ≤ 0`), (4.4a) and the asymptotic correctness for any `A`; for `p ≥ 1` through (4.1b) ([`PhiErrorEqIntegral.lean`](../../src/CORALean/ContDynamics/LinearSys/Krylov/Theorems/PhiErrorEqIntegral.lean)), as in [1]. **As printed:** `γ_m` enters as `\|γ_m\|`, `γ_m` for Arnoldi's positive subdiagonal; asymptotically correct is `‖L^p_m(t)v‖₂ = τ_{m+1,m}γ_m t^m/(m + p)! + O(t^{m+1})` as `t → 0⁺`, as (3.7) | `correct` |
| `Prop. 4` | `L_m(t)v = τ_{m+1,m}σt Σ_{j≥1} e_m*φ_j(σtT_m)e₁ (σtA)^{j-1}v_{m+1}` (5.1). | n/a — restated from Saad 1992 [42, Thm. 5.1] | `restated` |
| `Eq. 5.2` | `e^{σtT⁺_m}e₁ = [e^{σtT_m}e₁; τ_{m+1,m}σt(e_m*φ₁(σtT_m)e₁)]` for the extended matrix `T⁺_m` (5.2a). | n/a — restated from Saad 1992 [42, Prop. 2.1] | `restated` |
| `Prop. 5` | The error series (5.5a) of `L^p_m(t)v` and (5.5b) of the corrected `L^{p,+}_m(t)v`. | n/a — restated from Sidje's Expokit paper [44, Thm. 2] | `restated` |
| `Remark 4` | `e_m*φ_j(σtT_m)e₁ = γ_m(σt)^{m-1}/(m - 1 + j)! + O(t^m)` (5.6), the leading terms (5.7a), (5.7b) and the estimators Err₁ (5.8a), (5.8b). | [`PhiLeadingTermsIsBigO.lean`](../../src/CORALean/ContDynamics/LinearSys/Krylov/Theorems/PhiLeadingTermsIsBigO.lean) — any `A`, under (2.2), upper Hessenberg `T_m`, `v = V_me₁`; (5.6) through the Taylor expansion of `φ_j` ([`PhiSmulMulVecTaylorIsBigO.lean`](../../src/CORALean/ContDynamics/LinearSys/Krylov/Theorems/PhiSmulMulVecTaylorIsBigO.lean)), (2.3) and (2.5), (5.7a) and (5.7b) from (4.4a), (5.9a) and (5.6). **As printed:** (5.7a), (5.7b) are proved with the remainders `O(t^{m+1})`, `O(t^{m+2})`, one order more than the printed `O(t^m)`, `O(t^{m+1})` (each leading term is itself of the printed order, so the printed forms follow); (5.8a), (5.8b) are `≈` estimators, not claims | `correct` |
| `Thm. 3` | `L^{p,+}_m(t)v = τ_{m+1,m}γ_m(σt)^{m+1}/(m + p + 1)! Av_{m+1} + O(t^{m+2})` (5.9a), and in the nonexpansive case `‖L^{p,+}_m(t)v‖₂ ≤ ‖Av_{m+1}‖₂τ_{m+1,m}γ_m t^{m+1}/(m + p + 1)!` (5.9b), asymptotically correct. | [`PhiCorrectedErrorLeErrA.lean`](../../src/CORALean/ContDynamics/LinearSys/Krylov/Theorems/PhiCorrectedErrorLeErrA.lean) — `T⁺_m` (5.2a), `V⁺_m` (5.3) and `φ_p` (4.1a) written out, in the setting of `Thm. 1` without `‖v_{m+1}‖₂ = 1`; not through the restated `Prop. 5` but through the Krylov identity `AV⁺_m = V⁺_mT⁺_m + (Av_{m+1})e_{m+1}*` ([`CorrectedKrylovIdentity.lean`](../../src/CORALean/ContDynamics/LinearSys/Krylov/Theorems/CorrectedKrylovIdentity.lean)): (5.9a) is (4.4a) for it, and (3.1b) for it with `\|e_{m+1}*e^{σsT⁺_m}e₁\| ≤ τ_{m+1,m}\|γ_m\| s^m/m!` ([`NormExpCorrectedApplyLastLe.lean`](../../src/CORALean/ContDynamics/LinearSys/Krylov/Theorems/NormExpCorrectedApplyLastLe.lean)) and (4.1b) give (5.9b). **As printed:** `γ_m` enters as `\|γ_m\|`; asymptotically correct is `‖L^{p,+}_m(t)v‖₂` equal to the bound `+ O(t^{m+2})` as `t → 0⁺`, as (3.7) | `correct` |
| `Prop. 6` | Nonexpansive, `σ = 1`, `A` Hermitian: `\|δ_m(t)\| = δ_m(t) > 0` for `t > 0`, `‖L^p_m(t)v‖₂ ≤ τ_{m+1,m}t e_m*φ_{p+1}(tT_m)e₁` (5.10a) and `‖L^{p,+}_m(t)v‖₂ ≤ ‖Av_{m+1}‖₂τ_{m+1,m}t² e_m*φ_{p+2}(tT_m)e₁` (5.10b). | — | — |
| `Sec. 6` | The Hermite quadrature (6.2), the estimate (6.3) and the trapezoidal estimate (6.6) of the error integral. | n/a — approximations, not bounds | `not-a-claim` |
| `Eq. 6.4` | (Peano representation) `t/m Θ_m(t, t) - ∫₀ᵗΘ_m(s, t)v ds = ∫₀ᵗ s(t - s)^{m-1}/m! ∂^m_sΘ_m(s, t)v ds`, so the quadrature error is `O(t^{m+1})`. | — | — |
| `Eq. 6.5` | `∫₀ᵗΘ_m(s, t)v ds = 2t/(m + 1) D_m(t)v - t²/(m(m + 1)) D^{[2]}_m(t)v + O(t^{m+2})`, and the longer expansion after it. | — | — |
| `Eq. 6.8` | With `f(t) = \|δ_m(t)\| > 0` on `(0, T]` and its effective order `1 ≤ m̃ ≤ ρ(t) ≤ m - 1`: `t/m \|δ_m(t)\| ≤ ∫₀ᵗ\|δ_m(s)\|ds ≤ t/(m̃ + 1)\|δ_m(t)\| ≤ t/2 \|δ_m(t)\|`. | [`IntegralBoundsOfEffectiveOrder.lean`](../../src/CORALean/ContDynamics/LinearSys/Krylov/Theorems/IntegralBoundsOfEffectiveOrder.lean) — for any `f` continuous on `[0, T]`, differentiable on `(0, T)` and positive on `(0, T]`, `ρ(s) = f'(s)s/f(s)` (6.7) bounded on `(0, T)`, real `m̃`, `0 < t ≤ T`; proved through the monotonicity of `f(s)s^{-c}`, where [1] uses a mean value `ρ(t*)` | `correct` |
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
`Thm. 1` is formalized with `|δ_m(s)|`; the `Prop. 2` row stays `—` while its divided-difference
identity and its spectral hypothesis are not.

**CORA's use of `Thm. 1`, outside the nonexpansive case.** Err_a is a bound only when `W(σA) ⊆ ℂ⁻`;
the proof needs `‖E(t - s)‖₂ ≤ 1` in (3.1b) and `spec(σT_m) ⊆ ℂ⁻` in `Prop. 2`.

**`Thm. 1` — where CORA computes the bound.** `priv_subspace_Krylov_individual_Jawecki` computes
`errorBound = τ γ tFinal^m/m!` (with `tau = Hlast` and `gamma` the product of `H(i+1,i)`, as (2.5))
for whatever matrix it is handed and accepts the order once `‖v‖ · errorBound ≤ krylovError`;
nothing in `linearSys/reach` with `linAlg = 'krylov'` checks `A`, and the error box CORA adds is
`krylovError`. `priv_inputSolution_Krylov` and `priv_krylov_R_uTrans` hand it the integrator matrix
`C̃ = [A u; 0 0]`, whose field of values is never in `ℂ⁻` for `u ≠ 0` (at `x = (εu, 1)`,
`x*C̃x = ε²u*Au + ε‖u‖²` is positive for small `ε > 0`), at the start vector `[0ₙ; 1]` and order
`1 + krylovStep ≥ 2`.

**`Thm. 1` — the counterexample and the nonexpansive case.** For `A = [0 0; 1 1]` (`e₂*Ae₂ = 1`),
`u = e₁`, Arnoldi gives `V = [e₃ e₁]`, `τ₃,₂ = γ₂ = 1`, so Err_a at order `2` is `t²/2`, while the
second coordinate of `e^{tC̃}e₃`, which `V` cannot reach, is `e^t - 1 - t > t²/2` for every `t > 0`.
With `tFinal = timeStep = t` and `krylovError = t²/2` CORA accepts order `2`, and the box of radius
`krylovError` that `priv_krylov_R_uTrans` puts around `V e^{tT}e₁` misses the solution for the
constant input `u` (read from the source, not run). On the integrator matrix of a nonexpansive `A`
the bound does hold — the error integrand there is `E(t - s)` at `[w; 0]`, on which `C̃` acts as
`A`, and `T_m`'s first row vanishes, so its spectrum is `0` and that of a compression of `A` —
argued, not formalized.

**`Thm. 1` — the departures not witnessed.** Two further departures from the paper's setting are not
witnessed: the Arnoldi vectors are computed in floating point, so (2.2) and `V_m*V_m = I` hold only
to rounding (the paper's Table 8.1 shows the loss of orthogonality), and the happy breakdown test is
`H(j+1,j) <= eps`, absolute rather than relative to `‖A‖`.
[`JaweckiBoundCora.lean`](../../src/CORALean/ContDynamics/LinearSys/Krylov/Counterexamples/JaweckiBoundCora.lean)
