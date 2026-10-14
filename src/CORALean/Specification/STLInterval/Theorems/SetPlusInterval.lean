module

public import CORALean.Specification.STLInterval.Operations.PlusInterval
public import CORALean.Specification.STLInterval.Theorems.SetStlInterval
public import CORALean.Specification.STLInterval.Theorems.RawSetAdd
public import CORALean.Specification.STLInterval.Theorems.Basic

@[expose] public section

/-!
# `plus` with an `interval` denotes a sum

`I + J` for a box `J` denotes `I` plus the closed interval of `J`'s bounds.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open scoped Pointwise


-- =======================================  MAIN THEOREM  ======================================= --

/-- `plusInterval` denotes the sum with the closed interval `[inf, sup]`. -/
theorem STLInterval.set_plusInterval (I : STLInterval) (J : Real.Interval (Vec ℝ 1)) :
    (I.plusInterval J).set = I.set + Set.Icc (J.inf 0) (J.sup 0) := by -- --- PROOF ---
  cases I with
  | empty => simp [STLInterval.plusInterval, STLInterval.set]
  | nonempty l u lc rc a b c =>
    simp only [STLInterval.plusInterval]
    by_cases h : J.sup 0 < J.inf 0
    · rw [if_pos h]
      simp [STLInterval.set, Set.Icc_eq_empty_of_lt h]
    · rw [if_neg h, set_stlInterval, ← rawSet_closed_coe]
      have := rawSet_add (set_nonempty _ _ _ _ a b c) (rawSet_closed_nonempty (not_lt.1 h))
      simpa [STLInterval.set] using this

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
