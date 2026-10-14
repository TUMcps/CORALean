module

public import CORALean.ContSet.Interval.Real.Operations.Dirac

@[expose] public section

/-!
# `Interval.dirac` off zero

Where `0` is outside the interval (`0 < inf` or `sup < 0`, on a nonempty coordinate), `δ⁽ⁿ⁾`
vanishes on the whole interval and `dirac` returns the point `0`, for every `n`: exact there.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {m : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Interval.dirac_eq_zero_of_off (n : ℕ) (I : Interval (Vec ℝ m)) (i : Fin m)
    (hne : I.inf i ≤ I.sup i) (h : 0 < I.inf i ∨ I.sup i < 0) :
    (Interval.dirac n I).1 i = 0 ∧ (Interval.dirac n I).2 i = 0 := by -- --- PROOF ---
  classical
  -- both bounds have the same strict sign, so the signs sum to `2` or `-2`
  have hs : ((SignType.sign (I.inf i) : SignType) : ℤ) + ((SignType.sign (I.sup i) : SignType) : ℤ)
      = 2 ∨ ((SignType.sign (I.inf i) : SignType) : ℤ)
        + ((SignType.sign (I.sup i) : SignType) : ℤ) = -2 := by
    rcases h with h | h
    · left
      rw [sign_pos h, sign_pos (lt_of_lt_of_le h hne)]
      norm_num
    · right
      rw [sign_neg (lt_of_le_of_lt hne h), sign_neg h]
      norm_num
  unfold Interval.dirac
  rcases hs with e | e <;> by_cases h0 : n = 0 <;> by_cases h1 : n = 1 <;> simp [h0, h1, e]


end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
