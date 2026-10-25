module

public import CORALean.ContDynamics.LinearSys.Krylov.Theorems.NormExpApplyLastLe

@[expose] public section

/-!
# The computable upper bound Err_a on the Krylov error, in the nonexpansive case

[1, Thm. 1]: for `W(σA) ⊆ ℂ⁻`, the error of the Krylov approximation `S_m(t)v = V_me^{σtT_m}e₁`
(2.6) to `E(t)v = e^{σtA}v` satisfies `‖L_m(t)v‖₂ ≤ τ_{m+1,m}γ_m t^m/m!` (3.6), Err_a, with
`τ_{m+1,m}` from (2.2) and `γ_m = ∏_{j=1}^{m-1}(T_m)_{j+1,j}` (2.5). The setting of (2.1)-(2.2):
`|σ| = 1`, the Arnoldi basis `[V_m v_{m+1}]` orthonormal with `v = V_me₁`, `T_m` upper
Hessenberg, `τ_{m+1,m} ≥ 0`. As in [1]: (3.1b) bounds the error by `τ_{m+1,m}∫₀ᵗ|δ_m(s)|ds`;
(3.4) gives `W(σT_m) ⊆ W(σA) ⊆ ℂ⁻`, under which `|δ_m(s)| ≤ |γ_m| s^{m-1}/(m-1)!`; integrating
gives (3.6). `|γ_m|` is `γ_m` for Arnoldi's positive subdiagonal (Remark 1). Without the
nonexpansive hypothesis the bound fails (`Krylov.jawecki_bound_cora_counterexample`).

## Inputs
* `A` – matrix
* `V` – Krylov basis
* `T` – Hessenberg matrix
* `τ` – next subdiagonal entry
* `σ` – unit scaling
* `w` – next vector
* `t` – time

## Hypotheses
* `hK` – Krylov identity holds
* `hV` – basis has orthonormal columns
* `hVw` – next vector orthogonal to the basis
* `hτ` – subdiagonal entry nonnegative
* `hw` – next vector has unit norm
* `hH` – Hessenberg matrix is upper Hessenberg
* `hσ` – scaling has modulus one
* `hA` – scaled matrix has field of values in the left half-plane
* `ht` – time nonnegative

## Conclusion
* the Krylov error is at most the bound Err_a

## References

* [1] T. Jawecki, W. Auzinger and O. Koch. "Computable upper error bounds for Krylov approximations
      to matrix exponentials and associated φ-functions". BIT Numerical Mathematics, 2020.
-/

-- Authors:       Claude Opus 5.5
-- Written:       12-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix NormedSpace

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {n m : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- [1, Thm. 1]: for `W(σA) ⊆ ℂ⁻`, `‖e^{tσA}v - V_me^{tσT_m}e₁‖₂ ≤ τ_{m+1,m}|γ_m| t^m/m!`
(3.6), `t ≥ 0`, under (2.2) with `[V_m v_{m+1}]` orthonormal, `v = V_me₁`, upper Hessenberg
`T_m` and `|σ| = 1`; `V_m` has `m + 1` columns here. -/
theorem Krylov.error_le_errA (A : Mat ℂ n n) (V : Mat ℂ n (m + 1)) (T : Mat ℂ (m + 1) (m + 1))
    (τ : ℝ) (σ : ℂ) (w : Fin n → ℂ)
    (hK : A * V = V * T + (τ : ℂ) • vecMulVec w (Pi.single (Fin.last m) 1))
    (hV : Vᴴ * V = 1) (hVw : Vᴴ *ᵥ w = 0) (hτ : 0 ≤ τ)
    (hw : ‖(WithLp.toLp 2 w : EuclideanSpace ℂ (Fin n))‖ = 1)
    (hH : ∀ i k : Fin (m + 1), (k : ℕ) + 1 < i → T i k = 0) (hσ : ‖σ‖ = 1)
    (hA : ∀ x : Fin n → ℂ, (star x ⬝ᵥ ((σ • A) *ᵥ x)).re ≤ 0) {t : ℝ}
    (ht : 0 ≤ t) : -- --- CONCL ---
    let v := V *ᵥ Pi.single 0 1
    let γ := ∏ j : Fin m, T j.succ j.castSucc
    ‖(WithLp.toLp 2 (exp (t • (σ • A)) *ᵥ v - V *ᵥ (exp (t • (σ • T)) *ᵥ Pi.single 0 1)) :
        EuclideanSpace ℂ (Fin n))‖ ≤
      τ * ‖γ‖ * t ^ (m + 1) / (Nat.factorial (m + 1) : ℝ) := by -- --- PROOF ---
  intro v γ
  -- (3.4): `T_m = V_m*AV_m`, so `x*σT_mx = (V_mx)*σA(V_mx)` and `W(σT_m) ⊆ ℂ⁻`
  have hGal : Vᴴ * A * V = T := by
    rw [Matrix.mul_assoc, hK, Matrix.mul_add, ← Matrix.mul_assoc, hV, Matrix.one_mul,
      Matrix.mul_smul, mul_vecMulVec, hVw, zero_vecMulVec, smul_zero, add_zero]
  have hTW : ∀ x : Fin (m + 1) → ℂ, (star x ⬝ᵥ ((σ • T) *ᵥ x)).re ≤ 0 := by
    intro x
    have h := hA (V *ᵥ x)
    rw [Matrix.smul_mulVec, dotProduct_smul] at h
    rw [← hGal, Matrix.smul_mulVec, dotProduct_smul, ← Matrix.mulVec_mulVec,
      ← Matrix.mulVec_mulVec, dotProduct_mulVec, ← star_mulVec]
    exact h
  -- (3.1b)
  have h31 := Krylov.error_le_integral_delta A V T τ σ w hK hA hσ ht
  rw [Complex.norm_of_nonneg hτ, hw, mul_one] at h31
  -- `Prop. 2`'s estimate under the integral
  have hδ : ∀ s ∈ Set.Icc (0 : ℝ) t, ‖exp (s • (σ • T)) (Fin.last m) 0‖ ≤
      ‖γ‖ / (Nat.factorial m : ℝ) * s ^ m := fun s hs =>
    (Krylov.norm_exp_apply_last_le m T σ hH hTW hσ hs.1).trans (le_of_eq (by ring))
  have hδc : Continuous fun s : ℝ => ‖exp (s • (σ • T)) (Fin.last m) 0‖ :=
    ((exp_continuous.comp (continuous_id.smul continuous_const)).matrix_elem _ _).norm
  have hint : ∫ s in (0 : ℝ)..t, ‖exp (s • (σ • T)) (Fin.last m) 0‖ ≤
      ∫ s in (0 : ℝ)..t, ‖γ‖ / (Nat.factorial m : ℝ) * s ^ m :=
    intervalIntegral.integral_mono_on ht (hδc.intervalIntegrable (μ := MeasureTheory.volume) _ _)
      ((continuous_const.mul (continuous_pow m)).intervalIntegrable (μ := MeasureTheory.volume)
        _ _) hδ
  rw [intervalIntegral.integral_const_mul, integral_pow] at hint
  -- `∫₀ᵗ sᵐ/m! ds = t^{m+1}/(m+1)!`
  refine h31.trans ((mul_le_mul_of_nonneg_left hint hτ).trans (le_of_eq ?_))
  rw [Nat.factorial_succ]
  push_cast
  field_simp
  ring

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
