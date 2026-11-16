module

public import CORALean.ContDynamics.LinearSys.MatExp.Operations.CorrCoeff
public import CORALean.ContDynamics.LinearSys.MatExp.Operations.CorrCoeffLowTightFloat
public import CORALean.ContDynamics.LinearSys.MatExp.Theorems.CorrCoeffLowFloat

@[expose] public section

/-!
# `corrCoeffLowTight` is below the correction coefficient

`corrCoeff i = −(1 − 1/i)·a` with `a = i^(−1/(i−1)) = exp(−log i/(i − 1))` (`a^(i−1) = 1/i`).
The float `q` is above `1 − 1/i`, the exponent `x` above `−log i/(i − 1)` (the logarithm and the
quotient rounded down), so `expUp x` is above `a` and the rounded-up product above `(1 − 1/i)·a`.

## Inputs
* none

## Hypotheses
* `hi` – `2 ≤ i`

## Conclusion
* the float bound is at most `corrCoeff i`
-/

-- Authors:       Claude Opus 5.5
-- Written:       16-November-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {i : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem MatExp.corrCoeffLowTight_le (hi : 2 ≤ i) : -- --- CONCL ---
    toReal (MatExp.corrCoeffLowTight (𝕋 := 𝕋) i) ≤ Real.MatExp.corrCoeff i := by -- --- PROOF ---
  unfold MatExp.corrCoeffLowTight
  split_ifs with h
  swap
  · exact MatExp.corrCoeffLow_le hi
  have hi1 : (1:ℝ) < (i : ℝ) := by exact_mod_cast hi.trans_lt' one_lt_two
  have hipos : (0:ℝ) < (i : ℝ) := by linarith
  have hcast : ((i - 1 : ℕ) : ℝ) = (i : ℝ) - 1 := by
    have h1 : 1 ≤ i := by omega
    push_cast [Nat.cast_sub h1]; ring
  -- the real side: `corrCoeff i = −(1 − 1/i)·a`, `a = exp(−log i/(i − 1))`
  set a := Real.MatExp.corrCritical i with ha
  have ha0 : 0 ≤ a := Real.rpow_nonneg hipos.le _
  have hpow : a ^ (i - 1) = 1 / (i : ℝ) := by
    rw [ha, Real.MatExp.corrCritical,
      ← Real.rpow_natCast ((i : ℝ) ^ (-(1:ℝ) / ((i : ℝ) - 1))) (i - 1),
      ← Real.rpow_mul hipos.le, hcast, div_mul_cancel₀ _ (by linarith), Real.rpow_neg_one]
    exact (one_div _).symm
  have heq : Real.MatExp.corrCoeff i = -((1 - 1 / (i : ℝ)) * a) := by
    rw [Real.MatExp.corrCoeff, ← ha]
    have hsplit : a ^ i = a * a ^ (i - 1) := by
      rw [← pow_succ']; congr 1; omega
    rw [hsplit, hpow]; ring
  have haexp : a = Real.exp (-(Real.log (i : ℝ) / ((i : ℝ) - 1))) := by
    rw [ha, Real.MatExp.corrCritical, Real.rpow_def_of_pos hipos]; congr 1; ring
  -- the denominator `d` between `1` and `i`, the count `m` above `i − 1`
  set d : 𝕋 := maximum one (nsmulDown i one)
  have hd1 : 1 ≤ toReal d := by rw [toReal_maximum, toReal_one]; exact le_max_left _ _
  have hdi : toReal d ≤ (i : ℝ) := by
    have h' := nsmulDown_le i (one : 𝕋)
    rw [toReal_one, mul_one] at h'
    rw [toReal_maximum, toReal_one]; exact max_le hi1.le h'
  -- the count `m` of the exponent's quotient, above `i − 1`
  set m : 𝕋 := nsmulUp (i - 1) one
  have hm : (i : ℝ) - 1 ≤ toReal m := by
    have h' := le_nsmulUp (i - 1) (one : 𝕋)
    rw [toReal_one, mul_one, Nat.cast_sub (by omega), Nat.cast_one] at h'
    exact h'
  have hm0 : (0:ℝ) < toReal m := lt_of_lt_of_le (by linarith) hm
  -- the quotient `q ≥ 1 − 1/i`
  set q : 𝕋 := divUp m d
  have hq : 1 - 1 / (i : ℝ) ≤ toReal q := by
    have hdpos : (0:ℝ) < toReal d := lt_of_lt_of_le one_pos hd1
    have h1 : 1 - 1 / (i : ℝ) = ((i : ℝ) - 1) / (i : ℝ) := by field_simp
    rw [h1]
    calc ((i : ℝ) - 1) / (i : ℝ) ≤ ((i : ℝ) - 1) / toReal d :=
          div_le_div_of_nonneg_left (by linarith) hdpos hdi
      _ ≤ toReal m / toReal d := div_le_div_of_nonneg_right hm hdpos.le
      _ ≤ toReal q := div_le_divUp _ _ hdpos
  -- and `1 − 1/i ≥ 0`
  have hu0 : 0 ≤ 1 - 1 / (i : ℝ) := by
    rw [sub_nonneg, div_le_one hipos]; exact hi1.le
  -- the logarithm from below, `ℓ ≤ log i`, and the exponent `x ≥ −log i/(i − 1)`
  set ℓ : 𝕋 := logDown 16 64 d
  have hdmax : toReal d ≤ 2 ^ 16 / 2 := by
    have : (i : ℝ) ≤ 1024 := by exact_mod_cast h.2
    linarith
  have hℓ : toReal ℓ ≤ Real.log (i : ℝ) :=
    le_trans (logDown_le 16 64 d hd1 hdmax)
      (Real.log_le_log (lt_of_lt_of_le one_pos hd1) hdi)
  have hlog0 : 0 ≤ Real.log (i : ℝ) := Real.log_nonneg hi1.le
  -- the rounded-down quotient is below `log i/(i − 1)`, whatever the sign of `ℓ`
  have hquot : toReal (divDown ℓ m) ≤ Real.log (i : ℝ) / ((i : ℝ) - 1) := by
    refine le_trans (divDown_le_div ℓ m hm0) ?_
    rcases le_or_gt (toReal ℓ) 0 with hneg | hpos
    · exact le_trans (div_nonpos_of_nonpos_of_nonneg hneg hm0.le)
        (div_nonneg hlog0 (by linarith))
    · calc toReal ℓ / toReal m ≤ toReal ℓ / ((i : ℝ) - 1) :=
            div_le_div_of_nonneg_left hpos.le (by linarith) hm
        _ ≤ Real.log (i : ℝ) / ((i : ℝ) - 1) :=
            div_le_div_of_nonneg_right hℓ (by linarith)
  -- the exponent, capped at `0`, is above `−log i/(i − 1)`
  set x : 𝕋 := minimum zero (neg (divDown ℓ m))
  have hx : -(Real.log (i : ℝ) / ((i : ℝ) - 1)) ≤ toReal x := by
    rw [toReal_minimum, toReal_zero, toReal_neg]
    exact le_min (neg_nonpos.mpr (div_nonneg hlog0 (by linarith))) (neg_le_neg hquot)
  have hx0 : toReal x ≤ 2 ^ 16 / 2 := by
    rw [toReal_minimum, toReal_zero]
    exact le_trans (min_le_left _ _) (by norm_num)
  -- so `a ≤ expUp x`, and the product is above `(1 − 1/i)·a`
  have hae : a ≤ toReal (expUp 16 x) := by
    rw [haexp]; exact le_trans (Real.exp_le_exp.mpr hx) (le_expUp 16 x hx0)
  have hprod : (1 - 1 / (i : ℝ)) * a ≤ toReal (mulUp q (expUp 16 x)) :=
    le_trans (mul_le_mul hq hae ha0 (le_trans hu0 hq)) (mul_le_mulUp _ _)
  show toReal (neg (mulUp q (expUp 16 x))) ≤ _
  rw [toReal_neg, heq]
  exact neg_le_neg hprod

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
