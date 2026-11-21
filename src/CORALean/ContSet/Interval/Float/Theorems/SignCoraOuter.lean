module

public import CORALean.ContSet.Interval.Float.Operations.SignCora
public import CORALean.ContSet.Interval.Real.Theorems.Basic

@[expose] public section

/-!
# `Interval.signCora` contains the image under the sign

A certified `0 < inf` makes every point positive, a certified `inf = 0` every point nonnegative, and
`-1` bounds every sign from below; the upper bound is symmetric. No hypothesis.

## Inputs
* `I` – interval box

## Hypotheses
* none

## Conclusion
* the sign image of `I` lies in the result box
-/

-- Authors:       Claude Opus 5.5
-- Written:       20-November-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open Pointwise FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Interval.signCora_outer [SoundFloatArithmetic 𝕋] (I : Interval (Vec 𝕋 n)) : -- --- CONCL ---
    (fun x i => Real.sign (x i)) '' I.toSet ⊆ I.signCora.toSet := by -- --- PROOF ---
  rintro _ ⟨x, hx, rfl⟩ i
  have hx' : toReal (I.inf i) ≤ x i ∧ x i ≤ toReal (I.sup i) := hx i
  have hs := CORALean.Real.sign_monotone
  constructor
  -- the lower bound: `1` above a certified positive end, `0` at a certified zero, else `-1`
  · show toReal (if ltStrict zero (I.inf i) = true then one
      else if (le zero (I.inf i) && le (I.inf i) zero) = true then zero else neg one) ≤
        Real.sign (x i)
    split_ifs with h h2
    · have h0 := toReal_lt_of_ltStrict h
      rw [toReal_zero] at h0
      rw [toReal_one, Real.sign_of_pos (lt_of_lt_of_le h0 hx'.1)]
    · have h0 := toReal_le_of_le (Bool.and_eq_true_iff.mp h2).1
      rw [toReal_zero] at h0
      rw [toReal_zero, ← Real.sign_zero]
      exact hs (le_trans h0 hx'.1)
    · rw [toReal_neg, toReal_one]
      unfold Real.sign
      split_ifs <;> norm_num
  -- the upper bound, symmetric
  · show Real.sign (x i) ≤ toReal (if ltStrict (I.sup i) zero = true then neg one
      else if (le (I.sup i) zero && le zero (I.sup i)) = true then zero else one)
    split_ifs with h h2
    · have h0 := toReal_lt_of_ltStrict h
      rw [toReal_zero] at h0
      rw [toReal_neg, toReal_one, Real.sign_of_neg (lt_of_le_of_lt hx'.2 h0)]
    · have h0 := toReal_le_of_le (Bool.and_eq_true_iff.mp h2).1
      rw [toReal_zero] at h0
      rw [toReal_zero, ← Real.sign_zero]
      exact hs (le_trans hx'.2 h0)
    · rw [toReal_one]
      unfold Real.sign
      split_ifs <;> norm_num

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
