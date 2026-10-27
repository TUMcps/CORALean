module

public import CORALean.ContDynamics.LinearSys.Krylov.Theorems.ExpEqSumAddPhiMul
public import CORALean.ContDynamics.LinearSys.Krylov.Theorems.NormExpApplyLastLe

@[expose] public section

/-!
# The last entry of the first column of `e^{σsT⁺_m}`

[1, Thm. 3] bounds the defect of the corrected Krylov approximation through
`|e_{m+1}*e^{σsT⁺_m}e₁| ≤ τ_{m+1,m}∫₀ˢ|δ_m(r)|dr ≤ τ_{m+1,m}γ_m s^m/m!`, `T⁺_m = [T_m 0;
τ_{m+1,m}e_m* 0]` (5.2a), as (5.2b) reads it: `e_{m+1}*e^{σsT⁺_m}e₁ = στ_{m+1,m}∫₀ˢδ_m(r)dr`.
`T⁺_m[I; 0] = [I; 0]T_m + τ_{m+1,m}e_{m+1}e_m*`, so (2.8) writes `e^{σsT⁺_m}e₁ - [e^{σsT_m}e₁; 0]`
as `∫₀ˢe^{σ(s-r)T⁺_m}στ_{m+1,m}δ_m(r)e_{m+1}dr`, and `T⁺_me_{m+1} = 0`. `Prop. 2`'s estimate
under `W(σT_m) ⊆ ℂ⁻` bounds `|δ_m|`. `T_m` has size `m + 1` here.

## Inputs
* `T` – Hessenberg matrix
* `τ` – next subdiagonal entry
* `σ` – unit scaling
* `s` – time

## Hypotheses
* `hH` – Hessenberg matrix is upper Hessenberg
* `hT` – scaled matrix has field of values in the left half-plane
* `hσ` – scaling has modulus one
* `hs` – time nonnegative

## Conclusion
* the corrected exponential's last entry is bounded in the same way

## References

* [1] [T. Jawecki, W. Auzinger and O. Koch. "Computable upper error bounds for Krylov approximations
      to matrix exponentials and associated φ-functions". BIT Numerical Mathematics,
      2020.](../../../../../../references/2020/jawecki-bit-krylov-error-bounds.md)
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

variable {m : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- [1, Thm. 3]'s step: `|(e^{sσT⁺_m})_{m+1,1}| ≤ |τ_{m+1,m}||γ_m| s^m/m!` for `s ≥ 0`, upper
Hessenberg `T_m` with `W(σT_m) ⊆ ℂ⁻`, `|σ| = 1`; `T_m` has size `m + 1` here. -/
theorem Krylov.norm_exp_corrected_apply_last_le (T : Mat ℂ (m + 1) (m + 1)) (τ σ : ℂ)
    (hH : ∀ i k : Fin (m + 1), (k : ℕ) + 1 < i → T i k = 0)
    (hT : ∀ x : Fin (m + 1) → ℂ, (star x ⬝ᵥ ((σ • T) *ᵥ x)).re ≤ 0) (hσ : ‖σ‖ = 1) {s : ℝ}
    (hs : 0 ≤ s) : -- --- CONCL ---
    let Tp : Mat ℂ (m + 2) (m + 2) := Matrix.of fun i j =>
      Fin.lastCases (Fin.lastCases 0 (fun j' => if j' = Fin.last m then τ else 0) j)
        (fun i' => Fin.lastCases 0 (fun j' => T i' j') j) i
    ‖exp (s • (σ • Tp)) (Fin.last (m + 1)) 0‖ ≤
      ‖τ‖ * ‖∏ j : Fin m, T j.succ j.castSucc‖ * s ^ (m + 1) /
        (Nat.factorial (m + 1) : ℝ) := by -- --- PROOF ---
  intro Tp
  set V' : Mat ℂ (m + 2) (m + 1) := Matrix.of fun i j => if i = j.castSucc then 1 else 0
    with hV'
  set el : Fin (m + 2) → ℂ := Pi.single (Fin.last (m + 1)) 1 with hel
  set e₁ : Fin (m + 1) → ℂ := Pi.single 0 1 with he₁
  set δ : ℝ → ℂ := fun r => exp (r • (σ • T)) (Fin.last m) 0 with hδdef
  -- `T⁺_m[I; 0] = [I; 0]T_m + τe_{m+1}e_m*`
  have hK : Tp * V' = V' * T + τ • vecMulVec el (Pi.single (Fin.last m) 1) := by
    ext i j
    rcases Fin.eq_castSucc_or_eq_last i with ⟨i', rfl⟩ | rfl
    · simp [Tp, V', Matrix.mul_apply, hel, vecMulVec_apply, Fin.castSucc_inj]
    · simp [Tp, V', Matrix.mul_apply, hel, vecMulVec_apply, Pi.single_apply,
        (Fin.castSucc_ne_last _).symm]
  -- `y = e^{σrT⁺}e₁ - [I; 0]e^{σrT}e₁` solves `y' = σT⁺y + D`, `D = στδ e_{m+1}` (2.9)
  set y : ℝ → Fin (m + 2) → ℂ := fun r =>
    exp (r • (σ • Tp)) *ᵥ Pi.single 0 1 - V' *ᵥ (exp (r • (σ • T)) *ᵥ e₁) with hydef
  set D : ℝ → Fin (m + 2) → ℂ := fun r => (σ * τ * δ r) • el with hDdef
  have hδ : ∀ r, (exp (r • (σ • T)) *ᵥ e₁) (Fin.last m) = δ r := fun r => by
    rw [he₁, Matrix.mulVec_single_one]
    rfl
  -- its derivative, through the defect (2.9) of `T⁺_m[I; 0] = [I; 0]T_m + τe_{m+1}e_m*`
  have hy : ∀ r, HasDerivAt y ((σ • Tp) *ᵥ y r + D r) r := by
    intro r
    have h1 := Krylov.hasDerivAt_exp_smul_mulVec (σ • Tp) (Pi.single 0 1) r
    let LV : (Fin (m + 1) → ℂ) →L[ℝ] (Fin (m + 2) → ℂ) :=
      LinearMap.toContinuousLinearMap ((Matrix.mulVecLin V').restrictScalars ℝ)
    have h2 : HasDerivAt (fun r : ℝ => V' *ᵥ (exp (r • (σ • T)) *ᵥ e₁))
        (V' *ᵥ ((σ • T) *ᵥ (exp (r • (σ • T)) *ᵥ e₁))) r :=
      LV.hasFDerivAt.comp_hasDerivAt r (Krylov.hasDerivAt_exp_smul_mulVec (σ • T) e₁ r)
    refine (h1.sub h2).congr_deriv ?_
    have hdef := Krylov.defect_of_krylovIdentity Tp V' T τ σ el hK (exp (r • (σ • T)) *ᵥ e₁)
    rw [hδ] at hdef
    simp only [hydef, hDdef, Matrix.mulVec_sub, ← hdef, Matrix.smul_mulVec, Matrix.mulVec_smul]
    abel
  -- `y(0) = e₁ - [I; 0]e₁ = 0`
  have hy0 : y 0 = 0 := by
    show exp ((0 : ℝ) • (σ • Tp)) *ᵥ Pi.single 0 1 - V' *ᵥ (exp ((0 : ℝ) • (σ • T)) *ᵥ e₁) = 0
    simp only [zero_smul, exp_zero, Matrix.one_mulVec]
    ext i
    rcases Fin.eq_castSucc_or_eq_last i with ⟨i', rfl⟩ | rfl
    · simp [V', he₁, Pi.single_apply]
    · simp [V', he₁]
  have hδc : Continuous δ :=
    (exp_continuous.comp (continuous_id.smul continuous_const)).matrix_elem _ _
  have hDc : Continuous D := (continuous_const.mul hδc).smul continuous_const
  have hrep := Krylov.error_eq_integral_defect (σ • Tp) y D hy0 hy hDc s
  -- `T⁺e_{m+1} = 0`, so `e^{uσT⁺}e_{m+1} = e_{m+1}`
  have hTel : Tp *ᵥ el = 0 := by
    ext i
    rw [hel, Matrix.mulVec_single_one]
    rcases Fin.eq_castSucc_or_eq_last i with ⟨i', rfl⟩ | rfl <;> simp [Tp]
  have hfix : ∀ u : ℝ, exp (u • (σ • Tp)) *ᵥ el = el := by
    intro u
    have h : exp (u • (σ • Tp)) = ∑ j ∈ Finset.range 1, ((Nat.factorial j : ℝ)⁻¹) •
        (u • (σ • Tp)) ^ j + (∑' i : ℕ, ((Nat.factorial (i + 1) : ℝ)⁻¹) •
          (u • (σ • Tp)) ^ i) * (u • (σ • Tp)) ^ 1 := Krylov.exp_eq_sum_add_phi_mul _ 1
    rw [h, Matrix.add_mulVec, ← Matrix.mulVec_mulVec, pow_one, Matrix.smul_mulVec,
      Matrix.smul_mulVec, hTel, smul_zero, smul_zero, Matrix.mulVec_zero, add_zero]
    simp
  have hys : y s = (∫ r in (0 : ℝ)..s, σ * τ * δ r) • el := by
    rw [hrep]
    simp only [hDdef, Matrix.mulVec_smul, hfix]
    exact intervalIntegral.integral_smul_const _ _
  -- the last coordinate: `[I; 0]` has no last row
  have h1 : y s (Fin.last (m + 1)) = exp (s • (σ • Tp)) (Fin.last (m + 1)) 0 := by
    have h0 : (V' *ᵥ (exp (s • (σ • T)) *ᵥ e₁)) (Fin.last (m + 1)) = 0 := by
      simp [V', Matrix.mulVec, dotProduct, (Fin.castSucc_ne_last _).symm]
    simp only [hydef, Pi.sub_apply, h0, sub_zero, Matrix.mulVec_single_one]
    rfl
  have hlast : exp (s • (σ • Tp)) (Fin.last (m + 1)) 0 = ∫ r in (0 : ℝ)..s, σ * τ * δ r := by
    rw [← h1, hys]
    simp [hel]
  -- `|∫στδ| ≤ |τ|∫|δ|`, and `Prop. 2`'s estimate
  set c := ‖∏ j : Fin m, T j.succ j.castSucc‖ with hc
  rw [hlast]
  have hint : ∫ r in (0 : ℝ)..s, ‖σ * τ * δ r‖ ≤
      ∫ r in (0 : ℝ)..s, ‖τ‖ * (c / (Nat.factorial m : ℝ)) * r ^ m :=
    intervalIntegral.integral_mono_on hs
      ((continuous_const.mul hδc).norm.intervalIntegrable (μ := MeasureTheory.volume) _ _)
      ((continuous_const.mul (continuous_pow m)).intervalIntegrable (μ := MeasureTheory.volume)
        _ _) fun r hr => by
        rw [norm_mul, norm_mul, hσ, one_mul, mul_assoc]
        exact mul_le_mul_of_nonneg_left ((Krylov.norm_exp_apply_last_le m T σ hH hT hσ
          hr.1).trans (le_of_eq (by ring))) (norm_nonneg _)
  refine (intervalIntegral.norm_integral_le_integral_norm hs).trans (hint.trans (le_of_eq ?_))
  rw [intervalIntegral.integral_const_mul, integral_pow, Nat.factorial_succ]
  push_cast
  field_simp
  ring

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
