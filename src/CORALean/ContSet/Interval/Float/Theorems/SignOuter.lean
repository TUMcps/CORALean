module

public import CORALean.ContSet.Interval.Float.Operations.Sign
public import CORALean.ContSet.Interval.Real.Theorems.SignMonotone

@[expose] public section

/-!
# `Interval.sign` contains the image under the sign

The certified `le` is all that is needed: `0 ≤ inf` forces `sign x = 0` or `1`, and `sup ≤ 0`
forces `sign x ≤ 0`. No hypothesis.
-/

-- Authors:       Claude Opus 5.5
-- Written:       01-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open Pointwise FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Interval.sign_outer [SoundFloatArithmetic 𝕋] (I : Interval (Vec 𝕋 n)) :
    (fun x i => Real.sign (x i)) '' I.construct ⊆ I.sign.construct := by -- --- PROOF ---
  rintro _ ⟨x, hx, rfl⟩ i
  have hx' : toReal (I.inf i) ≤ x i ∧ x i ≤ toReal (I.sup i) := hx i
  have hs := CORALean.Real.sign_monotone
  constructor
  · show toReal (if le zero (I.inf i) = true then zero else neg one) ≤ Real.sign (x i)
    split_ifs with h
    · rw [toReal_zero, ← Real.sign_zero]
      exact hs (le_trans (toReal_zero (𝕋 := 𝕋) ▸ toReal_le_of_le h) hx'.1)
    · rw [toReal_neg, toReal_one]
      unfold Real.sign
      split_ifs <;> norm_num
  · show Real.sign (x i) ≤ toReal (if le (I.sup i) zero = true then zero else one)
    split_ifs with h
    · rw [toReal_zero, ← Real.sign_zero]
      exact hs (le_trans hx'.2 (toReal_zero (𝕋 := 𝕋) ▸ toReal_le_of_le h))
    · rw [toReal_one]
      unfold Real.sign
      split_ifs <;> norm_num


end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
