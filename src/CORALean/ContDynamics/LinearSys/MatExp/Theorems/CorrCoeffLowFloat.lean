module

public import CORALean.ContDynamics.LinearSys.MatExp.Operations.CorrCoeff
public import CORALean.ContDynamics.LinearSys.MatExp.Operations.CorrCoeffLowFloat
public import Mathlib.Algebra.Order.Ring.Star

@[expose] public section

/-!
# `MatExp.corrCoeffLow` bounds the correction coefficient from below

At the stationary point `a = i^(-1/(i-1))`, `a^(i-1) = 1/i`, so
`corrCoeff i = a·(a^(i-1) - 1) = -(1 - 1/i)·a`. Bernoulli's inequality gives
`(1 - 1/i)^(i-1) ≥ 1/i = a^(i-1)`, hence `a ≤ 1 - 1/i` and the coefficient is at
least `-(1 - 1/i)²`, which the float value rounds below.
-/

-- Authors:       Claude Opus 5.5
-- Written:       24-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {i : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- The exact bound: `corrCoeff i ≥ -(1 - 1/i)²`. -/
theorem aux_neg_sq_le_corrCoeff (hi : 2 ≤ i) :
    -((1 - 1 / (i : ℝ)) * (1 - 1 / (i : ℝ))) ≤ Real.MatExp.corrCoeff i := by -- --- PROOF ---
  have hi1 : (1:ℝ) < (i : ℝ) := by exact_mod_cast hi.trans_lt' one_lt_two
  have hipos : (0:ℝ) < (i : ℝ) := by linarith
  have hcast : ((i - 1 : ℕ) : ℝ) = (i : ℝ) - 1 := by
    have h1 : 1 ≤ i := by omega
    push_cast [Nat.cast_sub h1]; ring
  set a := Real.MatExp.corrCritical i with ha
  have ha0 : 0 ≤ a := Real.rpow_nonneg hipos.le _
  -- the stationary point solves `a ^ (i - 1) = 1/i`
  have hpow : a ^ (i - 1) = 1 / (i : ℝ) := by
    rw [ha, Real.MatExp.corrCritical,
      ← Real.rpow_natCast ((i : ℝ) ^ (-(1:ℝ) / ((i : ℝ) - 1))) (i - 1),
      ← Real.rpow_mul hipos.le, hcast, div_mul_cancel₀ _ (by linarith), Real.rpow_neg_one]
    exact (one_div _).symm
  have hu0 : 0 ≤ 1 - 1 / (i : ℝ) := by
    rw [sub_nonneg, div_le_one hipos]; exact hi1.le
  -- Bernoulli: `(1 - 1/i)^(i-1) ≥ 1 - (i-1)/i = 1/i`
  have hbern : a ^ (i - 1) ≤ (1 - 1 / (i : ℝ)) ^ (i - 1) := by
    have hb := one_add_mul_le_pow (a := -(1 / (i : ℝ)))
      (by have : 1 / (i : ℝ) ≤ 1 := by rw [div_le_one hipos]; exact hi1.le
          linarith) (i - 1)
    rw [hpow, ← sub_eq_add_neg] at *
    refine le_trans (le_of_eq ?_) hb
    rw [hcast]; field_simp; ring
  have hau : a ≤ 1 - 1 / (i : ℝ) := (pow_le_pow_iff_left₀ ha0 hu0 (by omega)).mp hbern
  -- `corrCoeff i = a · (a^(i-1) - 1) = -(1 - 1/i) · a`
  have heq : Real.MatExp.corrCoeff i = -((1 - 1 / (i : ℝ)) * a) := by
    rw [Real.MatExp.corrCoeff, ← ha]
    have hsplit : a ^ i = a * a ^ (i - 1) := by
      rw [← pow_succ']; congr 1; omega
    rw [hsplit, hpow]; ring
  rw [heq, neg_le_neg_iff]
  exact mul_le_mul_of_nonneg_left hau hu0


-- =======================================  MAIN THEOREM  ======================================= --

theorem MatExp.corrCoeffLow_le (hi : 2 ≤ i) :
    toReal (MatExp.corrCoeffLow (𝕋 := 𝕋) i) ≤ Real.MatExp.corrCoeff i := by -- --- PROOF ---
  have hi1 : (1:ℝ) < (i : ℝ) := by exact_mod_cast hi.trans_lt' one_lt_two
  have hipos : (0:ℝ) < (i : ℝ) := by linarith
  -- the denominator is held between `1` and `i`, the numerator above `i - 1`
  set d : 𝕋 := maximum one (nsmulDown i one)
  have hd1 : 1 ≤ toReal d := by rw [toReal_maximum, toReal_one]; exact le_max_left _ _
  have hdi : toReal d ≤ (i : ℝ) := by
    have h := nsmulDown_le i (one : 𝕋)
    rw [toReal_one, mul_one] at h
    rw [toReal_maximum, toReal_one]; exact max_le hi1.le h
  have hnum : (i : ℝ) - 1 ≤ toReal (nsmulUp (i - 1) (one : 𝕋)) := by
    have h := le_nsmulUp (i - 1) (one : 𝕋)
    rw [toReal_one, mul_one, Nat.cast_sub (by omega), Nat.cast_one] at h
    exact h
  -- so the quotient is above `(i - 1)/i`, and its rounded square above `(1 - 1/i)²`
  set q : 𝕋 := divUp (nsmulUp (i - 1) one) d
  have hq : 1 - 1 / (i : ℝ) ≤ toReal q := by
    have hdpos : (0:ℝ) < toReal d := lt_of_lt_of_le one_pos hd1
    have h1 : 1 - 1 / (i : ℝ) = ((i : ℝ) - 1) / (i : ℝ) := by field_simp
    rw [h1]
    calc ((i : ℝ) - 1) / (i : ℝ) ≤ ((i : ℝ) - 1) / toReal d :=
          div_le_div_of_nonneg_left (by linarith) hdpos hdi
      _ ≤ toReal (nsmulUp (i - 1) (one : 𝕋)) / toReal d :=
          div_le_div_of_nonneg_right hnum hdpos.le
      _ ≤ toReal q := div_le_divUp _ _ hdpos
  have hu0 : 0 ≤ 1 - 1 / (i : ℝ) := by
    rw [sub_nonneg, div_le_one hipos]; exact hi1.le
  have hsq : (1 - 1 / (i : ℝ)) * (1 - 1 / (i : ℝ)) ≤ toReal (mulUp q q) :=
    le_trans (mul_le_mul hq hq hu0 (le_trans hu0 hq)) (mul_le_mulUp q q)
  show toReal (neg (mulUp q q)) ≤ _
  rw [toReal_neg]
  exact le_trans (neg_le_neg hsq) (aux_neg_sq_le_corrCoeff hi)

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
