import CORALean.ContDynamics.LinearSys.Krylov.Theorems.ErrorLeIntegralDelta
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# The last entry of the first column of `e^{σsT_m}`, for a Hessenberg `T_m` with `W(σT_m) ⊆ ℂ⁻`

[1, Prop. 2]'s estimate `|δ_m(s)| ≤ s^{m-1}/(m-1)! γ_m` (3.5), `δ_m(s) = e_m*e^{σsT_m}e₁`,
`γ_m = ∏_{j=1}^{m-1}(T_m)_{j+1,j}`, for an upper Hessenberg `T_m`, `|σ| = 1` and
`W(σT_m) ⊆ ℂ⁻` in place of [1]'s `spec(σT_m) ⊆ ℂ⁻`, and without divided differences. The
leading `(m-1) × (m-1)` block `T'` of `T_m` satisfies a Krylov identity (2.2) of `T_m` itself,
`T_m V' = V'T' + (T_m)_{m,m-1} e_m e_{m-1}*` with `V' = [I; 0]`, and `V'` has no last row, so
`|δ_m(s)|` is at most the error of that Krylov approximation; (3.1b) bounds it by
`|(T_m)_{m,m-1}|∫₀ˢ|δ'(r)|dr`, and induction on `m` gives the bound. In the nonexpansive case
`W(σT_m) ⊆ W(σA) ⊆ ℂ⁻` (3.4), so this is the form [1, Thm. 1] uses.

## References

* [1] T. Jawecki, W. Auzinger, O. Koch. "Computable upper error bounds for Krylov approximations
  to matrix exponentials and associated φ-functions". BIT Numerical Mathematics, 60(1):157-197,
  2020.
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


-- =======================================  MAIN THEOREM  ======================================= --

/-- [1, Prop. 2], the estimate (3.5) under `W(σT_m) ⊆ ℂ⁻`: `|(e^{sσT_m})_{m,1}| ≤
|∏_j (T_m)_{j+1,j}| s^{m-1}/(m-1)!` for upper Hessenberg `T_m`, `|σ| = 1`, `s ≥ 0`, at `T_m`
of size `m + 1` here. -/
theorem Krylov.norm_exp_apply_last_le (m : ℕ) (T : Mat ℂ (m + 1) (m + 1)) (σ : ℂ)
    (hH : ∀ i k : Fin (m + 1), (k : ℕ) + 1 < i → T i k = 0)
    (hT : ∀ x : Fin (m + 1) → ℂ, (star x ⬝ᵥ ((σ • T) *ᵥ x)).re ≤ 0) (hσ : ‖σ‖ = 1) {s : ℝ}
    (hs : 0 ≤ s) :
    ‖exp (s • (σ • T)) (Fin.last m) 0‖ ≤
      ‖∏ j : Fin m, T j.succ j.castSucc‖ * s ^ m / (Nat.factorial m : ℝ) := by -- --- PROOF ---
  induction m generalizing s with
  | zero =>
    -- a contraction keeps the entry of `e₁`'s image below `‖e₁‖₂ = 1`
    have h := Krylov.norm_exp_smul_mulVec_le (σ • T) hT (Pi.single 0 1) hs
    have hle := PiLp.norm_apply_le
      (WithLp.toLp 2 (exp (s • (σ • T)) *ᵥ Pi.single 0 1) : EuclideanSpace ℂ (Fin 1)) 0
    have h1 : ‖(WithLp.toLp 2 (Pi.single 0 1 : Fin 1 → ℂ) : EuclideanSpace ℂ (Fin 1))‖ = 1 := by
      exact (PiLp.norm_single 2 (fun _ => ℂ) 0 1).trans norm_one
    simp only [Finset.univ_eq_empty, Finset.prod_empty, norm_one, pow_zero, Nat.factorial_zero,
      Nat.cast_one, div_one, mul_one]
    rw [h1] at h
    refine le_trans (le_of_eq ?_) (hle.trans h)
    show _ = ‖(exp (s • (σ • T)) *ᵥ Pi.single 0 1) 0‖
    rw [Matrix.mulVec_single_one]
    rfl
  | succ m ih =>
    -- the leading block, the embedding `V' = [I; 0]` and the coupling entry
    set T' : Mat ℂ (m + 1) (m + 1) := Matrix.of fun i j => T i.castSucc j.castSucc with hT'
    set V' : Mat ℂ (m + 2) (m + 1) := Matrix.of fun i j => if i = j.castSucc then 1 else 0
      with hV'
    set β := T (Fin.last (m + 1)) (Fin.last m).castSucc with hβ
    set w : Fin (m + 2) → ℂ := Pi.single (Fin.last (m + 1)) 1 with hw
    have hK : T * V' = V' * T' + β • vecMulVec w (Pi.single (Fin.last m) 1) := by
      ext i j
      simp only [Matrix.mul_apply, hV', hT', Matrix.of_apply, Matrix.add_apply, Matrix.smul_apply,
        vecMulVec_apply, hw, mul_ite, mul_one, mul_zero, ite_mul, one_mul, zero_mul]
      rw [Finset.sum_ite_eq']
      -- rows above the last copy `T'`; the last row is `β` at column `m`, else `0` (Hessenberg)
      rcases Fin.eq_castSucc_or_eq_last i with ⟨i', rfl⟩ | rfl
      · simp [Fin.castSucc_inj, Pi.single_apply, Fin.castSucc_ne_last]
      · simp only [Finset.mem_univ, if_true, (Fin.castSucc_ne_last _).symm, if_false,
          Finset.sum_const_zero, zero_add, Pi.single_apply, smul_eq_mul]
        by_cases hj : j = Fin.last m
        · subst hj; simp [hβ]
        · simp only [hj, if_false, mul_zero]
          apply hH
          have := Fin.val_lt_last hj
          simp only [Fin.val_castSucc, Fin.val_last] at this ⊢
          omega
    -- `x*σT'x = (V'x)*σT(V'x)`, so `W(σT') ⊆ ℂ⁻`
    have hne : ∀ i : Fin (m + 1), ¬Fin.last (m + 1) = i.castSucc := fun i h =>
      Fin.castSucc_ne_last i h.symm
    have hVV : V'ᴴ * V' = 1 := by
      ext i j
      simp [Matrix.mul_apply, hV', conjTranspose_apply, Matrix.one_apply, Fin.castSucc_inj,
        eq_comm]
    have hVw : V'ᴴ *ᵥ w = 0 := by
      ext i
      simp [mulVec, dotProduct, hV', hw, conjTranspose_apply, Pi.single_apply, hne]
    -- the Galerkin form `T' = V'*TV'`, as in (3.4)
    have hGal : V'ᴴ * T * V' = T' := by
      rw [Matrix.mul_assoc, hK, Matrix.mul_add, ← Matrix.mul_assoc, hVV, Matrix.one_mul,
        Matrix.mul_smul, mul_vecMulVec, hVw, zero_vecMulVec, smul_zero, add_zero]
    have hT'W : ∀ x : Fin (m + 1) → ℂ, (star x ⬝ᵥ ((σ • T') *ᵥ x)).re ≤ 0 := by
      intro x
      have h := hT (V' *ᵥ x)
      rw [Matrix.smul_mulVec, dotProduct_smul] at h
      rw [← hGal, Matrix.smul_mulVec, dotProduct_smul, ← Matrix.mulVec_mulVec,
        ← Matrix.mulVec_mulVec, dotProduct_mulVec, ← star_mulVec]
      exact h
    -- `T'` is Hessenberg and `‖e_{m+1}‖₂ = 1`
    have hH' : ∀ i k : Fin (m + 1), (k : ℕ) + 1 < i → T' i k = 0 := fun i k hik => hH _ _ hik
    have hnw : ‖(WithLp.toLp 2 w : EuclideanSpace ℂ (Fin (m + 2)))‖ = 1 := by
      exact (PiLp.norm_single 2 (fun _ => ℂ) (Fin.last (m + 1)) 1).trans norm_one
    -- (3.1b) for that Krylov approximation of `T` itself
    have h31 := Krylov.error_le_integral_delta T V' T' β σ w hK hT hσ hs
    rw [hnw, mul_one] at h31
    have hv : V' *ᵥ Pi.single 0 1 = Pi.single 0 1 := by
      ext i
      simp [hV', Pi.single_apply]
    simp only [hv] at h31
    -- its last coordinate is `δ_m(s)`, `V'` having no last row
    have hcoord : ‖exp (s • (σ • T)) (Fin.last (m + 1)) 0‖ ≤ ‖β‖ *
        ∫ r in (0 : ℝ)..s, ‖exp (r • (σ • T')) (Fin.last m) 0‖ := by
      refine le_trans (le_of_eq ?_) ((PiLp.norm_apply_le _ (Fin.last (m + 1))).trans h31)
      show _ = ‖(exp (s • (σ • T)) *ᵥ Pi.single 0 1 -
        V' *ᵥ (exp (s • (σ • T')) *ᵥ Pi.single 0 1)) (Fin.last (m + 1))‖
      simp [hV', mulVec, dotProduct, (Fin.castSucc_ne_last _).symm]
    -- the induction hypothesis under the integral
    set c := ‖∏ j : Fin m, T' j.succ j.castSucc‖ with hc
    have hIH : ∀ r ∈ Set.Icc (0 : ℝ) s, ‖exp (r • (σ • T')) (Fin.last m) 0‖ ≤
        c / (Nat.factorial m : ℝ) * r ^ m := by
      intro r hr
      have h := ih T' hH' hT'W hr.1
      exact h.trans (le_of_eq (by ring))
    have hδc : Continuous fun r : ℝ => ‖exp (r • (σ • T')) (Fin.last m) 0‖ :=
      ((exp_continuous.comp (continuous_id.smul continuous_const)).matrix_elem _ _).norm
    have hint : ∫ r in (0 : ℝ)..s, ‖exp (r • (σ • T')) (Fin.last m) 0‖ ≤
        ∫ r in (0 : ℝ)..s, c / (Nat.factorial m : ℝ) * r ^ m := intervalIntegral.integral_mono_on hs
      (hδc.intervalIntegrable (μ := MeasureTheory.volume) _ _)
      ((continuous_const.mul (continuous_pow m)).intervalIntegrable (μ := MeasureTheory.volume)
        _ _) hIH
    rw [intervalIntegral.integral_const_mul, integral_pow] at hint
    -- `∏_{j ≤ m} = (∏_{j < m}) · β`
    have hprod : ∏ j : Fin (m + 1), T j.succ j.castSucc = (∏ j : Fin m, T' j.succ j.castSucc) * β
        := by
      rw [Fin.prod_univ_castSucc]
      rfl
    rw [hprod, norm_mul, ← hc]
    refine hcoord.trans ((mul_le_mul_of_nonneg_left hint (norm_nonneg β)).trans (le_of_eq ?_))
    rw [Nat.factorial_succ]
    push_cast
    field_simp
    ring

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
