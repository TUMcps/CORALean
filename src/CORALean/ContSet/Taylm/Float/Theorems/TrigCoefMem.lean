module

public import CORALean.ContSet.Taylm.Float.Operations.TrigCoef
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv

@[expose] public section

/-!
# `Taylm.trigCoef` encloses the Taylor coefficients of `sin` and `cos`

By induction on `k`: `iteratedDeriv (k+1) sin = iteratedDeriv k cos` and
`iteratedDeriv (k+1) cos = -iteratedDeriv k sin`, and `(k+1)! = (k+1) k!`, so each coefficient is
the previous one of the other function over `k + 1`, which the division encloses.
-/

-- Authors:       Claude Opus 5.5
-- Written:       02-October-2026
-- Last update:   14-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋]


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- A value between `l` and `u`, divided by `k + 1` between its two roundings. -/
theorem Taylm.aux_div_succ_mem {l u : 𝕋} {v : ℝ} (hl : toReal l ≤ v) (hu : v ≤ toReal u)
    (k : ℕ) : -- --- STMT ---
    toReal (minimum (divDown l (nsmulUp (k + 1) one))
        (divDown l (maximum one (nsmulDown (k + 1) one)))) ≤ v / ((k + 1 : ℕ) : ℝ) ∧
      v / ((k + 1 : ℕ) : ℝ) ≤ toReal (maximum (divUp u (nsmulUp (k + 1) one))
        (divUp u (maximum one (nsmulDown (k + 1) one)))) := by -- --- PROOF ---
  set m : ℝ := ((k + 1 : ℕ) : ℝ)
  have hm1 : (1 : ℝ) ≤ m := by simp only [m]; exact_mod_cast Nat.succ_pos k
  -- the two roundings of `k + 1`, the lower one floored at one
  have hU : m ≤ toReal (nsmulUp (k + 1) (one : 𝕋)) := by
    have := le_nsmulUp (k + 1) (one : 𝕋); rw [toReal_one, mul_one] at this; exact this
  have hD1 : (1 : ℝ) ≤ toReal (maximum one (nsmulDown (k + 1) (one : 𝕋))) := by
    rw [toReal_maximum, toReal_one]; exact le_max_left _ _
  have hDm : toReal (maximum one (nsmulDown (k + 1) (one : 𝕋))) ≤ m := by
    have := nsmulDown_le (k + 1) (one : 𝕋)
    rw [toReal_one, mul_one] at this
    rw [toReal_maximum, toReal_one]; exact max_le hm1 this
  set mU := toReal (nsmulUp (k + 1) (one : 𝕋))
  set mD := toReal (maximum one (nsmulDown (k + 1) (one : 𝕋)))
  have hm0 : 0 < m := by linarith
  have hU0 : 0 < mU := by linarith
  have hD0 : 0 < mD := by linarith
  -- `s / m` lies between `s / mU` and `s / mD`, whatever the sign of `s`
  have hbet : ∀ s : ℝ, min (s / mU) (s / mD) ≤ s / m ∧ s / m ≤ max (s / mU) (s / mD) := by
    intro s
    have i1 : m⁻¹ ≤ mD⁻¹ := inv_anti₀ hD0 hDm
    have i2 : mU⁻¹ ≤ m⁻¹ := inv_anti₀ hm0 hU
    simp only [div_eq_mul_inv]
    rcases le_total 0 s with hs | hs
    · exact ⟨min_le_of_left_le (mul_le_mul_of_nonneg_left i2 hs),
        le_max_of_le_right (mul_le_mul_of_nonneg_left i1 hs)⟩
    · exact ⟨min_le_of_right_le (mul_le_mul_of_nonpos_left i1 hs),
        le_max_of_le_left (mul_le_mul_of_nonpos_left i2 hs)⟩
  simp only [toReal_minimum, toReal_maximum]
  constructor
  · refine le_trans (min_le_min (divDown_le_div _ _ hU0) (divDown_le_div _ _ hD0))
      (le_trans (hbet _).1 (div_le_div_of_nonneg_right hl hm0.le))
  · exact le_trans (div_le_div_of_nonneg_right hu hm0.le)
      (le_trans (hbet _).2 (max_le_max (div_le_divUp _ _ hU0) (div_le_divUp _ _ hD0)))


-- =======================================  MAIN THEOREM  ======================================= --

theorem Taylm.trigCoef_mem (p : ℕ) (c : 𝕋) (k : ℕ) : -- --- STMT ---
    (toReal (Taylm.trigCoef p c k).1.inf ≤ iteratedDeriv k Real.sin (toReal c) / (k.factorial : ℝ) ∧
      iteratedDeriv k Real.sin (toReal c) / (k.factorial : ℝ) ≤ toReal (Taylm.trigCoef p c k).1.sup)
    ∧ (toReal (Taylm.trigCoef p c k).2.inf ≤
        iteratedDeriv k Real.cos (toReal c) / (k.factorial : ℝ) ∧
      iteratedDeriv k Real.cos (toReal c) / (k.factorial : ℝ) ≤
        toReal (Taylm.trigCoef p c k).2.sup) := by -- --- PROOF ---
  induction k with
  | zero =>
    simp only [iteratedDeriv_zero, Nat.factorial_zero, Nat.cast_one, div_one, Taylm.trigCoef]
    exact ⟨⟨sinDown_le p c, le_sinUp p c⟩, ⟨cosDown_le p c, le_cosUp p c⟩⟩
  | succ k ih =>
    -- `(k+1)! = (k+1) k!`, and the derivative of one function is the other
    have hf : ∀ g : ℝ → ℝ, iteratedDeriv (k + 1) g (toReal c) / ((k + 1).factorial : ℝ) =
        iteratedDeriv (k + 1) g (toReal c) / (k.factorial : ℝ) / ((k + 1 : ℕ) : ℝ) := by
      intro g
      rw [Nat.factorial_succ, Nat.cast_mul, div_div, mul_comm]
    have hs : iteratedDeriv (k + 1) Real.sin (toReal c) = iteratedDeriv k Real.cos (toReal c) := by
      rw [Real.iteratedDeriv_add_one_sin]
    have hc : iteratedDeriv (k + 1) Real.cos (toReal c) =
        -iteratedDeriv k Real.sin (toReal c) := by
      rw [Real.iteratedDeriv_add_one_cos, Pi.neg_apply]
    have hns : toReal (neg (Taylm.trigCoef p c k).1.sup) ≤
        -iteratedDeriv k Real.sin (toReal c) / (k.factorial : ℝ) := by
      rw [toReal_neg, neg_div]; exact neg_le_neg ih.1.2
    have hns' : -iteratedDeriv k Real.sin (toReal c) / (k.factorial : ℝ) ≤
        toReal (neg (Taylm.trigCoef p c k).1.inf) := by
      rw [toReal_neg, neg_div]; exact neg_le_neg ih.1.1
    rw [hf, hf, hs, hc]
    exact ⟨Taylm.aux_div_succ_mem ih.2.1 ih.2.2 k, Taylm.aux_div_succ_mem hns hns' k⟩

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
