module

public import CORALean.ContSet.Interval.Float.Operations.RoundAwayInt
public import CORALean.ContSet.Interval.Real.Operations.RoundAway

@[expose] public section

/-!
# `roundAwayInt` is `roundAway`

On a rational, read in ℝ, the computable integer is the exact layer's rounding.
-/

-- Authors:       Claude Opus 5.5
-- Written:       12-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float


-- =======================================  MAIN THEOREM  ======================================= --

theorem roundAwayInt_cast (q : ℚ) :
    ((roundAwayInt q : ℤ) : ℝ) = CORALean.Real.roundAway (q : ℝ) := by -- --- PROOF ---
  unfold roundAwayInt CORALean.Real.roundAway
  by_cases h : 0 ≤ q
  · have h' : (0 : ℝ) ≤ q := by exact_mod_cast h
    rw [if_pos h, if_pos h']
    have := Rat.floor_cast (α := ℝ) (q + 1 / 2)
    push_cast at this
    rw [← this]
  · have h' : ¬ (0 : ℝ) ≤ q := by exact_mod_cast h
    rw [if_neg h, if_neg h']
    have := Rat.floor_cast (α := ℝ) (-q + 1 / 2)
    push_cast at this ⊢
    rw [← this]

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
