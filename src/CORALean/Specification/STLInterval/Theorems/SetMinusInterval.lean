module

public import CORALean.Specification.STLInterval.Operations.MinusInterval
public import CORALean.Specification.STLInterval.Theorems.SetStlInterval
public import CORALean.Specification.STLInterval.Theorems.RawSetSub
public import CORALean.Specification.STLInterval.Theorems.RawSetClamp
public import CORALean.Specification.STLInterval.Theorems.Basic

@[expose] public section

/-!
# `minus` with an `interval` denotes a difference

`I - J` for a box `J` denotes the nonnegative differences with the closed interval of `J`'s bounds.

## Inputs
* `I` – interval
* `J` – real interval

## Hypotheses
* none

## Conclusion
* the difference denotes the nonnegative differences with the real interval
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open scoped Pointwise


-- =======================================  MAIN THEOREM  ======================================= --

/-- `minusInterval` denotes the differences with `[inf, sup]`, at least `0`. -/
theorem STLInterval.set_minusInterval (I : STLInterval)
    (J : Real.Interval (Vec ℝ 1)) : -- --- CONCL ---
    (I.minusInterval J).set =
      (I.set - Set.Icc (J.inf 0) (J.sup 0)) ∩ Set.Ici 0 := by -- --- PROOF ---
  cases I with
  | empty => simp [STLInterval.minusInterval, STLInterval.set]
  | nonempty l u lc rc a b c _ =>
    simp only [STLInterval.minusInterval]
    by_cases h : J.sup 0 < J.inf 0
    · rw [if_pos h]
      simp [STLInterval.set, Set.Icc_eq_empty_of_lt h]
    · rw [if_neg h]
      have := rawSet_sub (rawSet_nonempty_of _ _ _ _ a b c) (rawSet_closed_nonempty (not_lt.1 h))
      rw [rawSet_closed_coe] at this
      simp only [Bool.and_true] at this
      show _ = (rawSet l u lc rc - _) ∩ Set.Ici 0
      rw [← this, rawSet_clamp]
      split_ifs <;> exact set_stlInterval _ _ _ _ _

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
