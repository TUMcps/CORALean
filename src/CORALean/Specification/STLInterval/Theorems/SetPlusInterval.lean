module

public import CORALean.Specification.STLInterval.Operations.PlusInterval
public import CORALean.Specification.STLInterval.Theorems.Basic
public import CORALean.Specification.STLInterval.Theorems.RawSetAdd
public import CORALean.Specification.STLInterval.Theorems.RawSetNonemptyOfFields
public import CORALean.Specification.STLInterval.Theorems.SetStlInterval

@[expose] public section

/-!
# `plus` with an `interval` denotes a sum

`I + J` for a box `J` denotes `I` plus the closed interval of `J`'s bounds.

## Inputs
* `I` – interval
* `J` – real interval

## Hypotheses
* `hc` – the lower bound stays nonnegative

## Conclusion
* the sum denotes the times plus the real interval
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   15-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Float FloatOps SoundFloatArithmetic
open scoped Pointwise


-- =======================================  MAIN THEOREM  ======================================= --

/-- `plusInterval` denotes the sum with the closed interval `[inf, sup]`. -/
theorem STLInterval.set_plusInterval (I : STLInterval ℝ) (J : Real.Interval (Vec ℝ 1))
    (hc : I ≠ .empty → ¬ toReal (J.sup 0) < toReal (J.inf 0) →
      0 ≤ toReal (addDown I.lowerBound (J.inf 0))) : -- --- CONCL ---
    (I.plusInterval J hc).set = I.set + Set.Icc (J.inf 0) (J.sup 0) := by -- --- PROOF ---
  cases I with
  | empty => simp [STLInterval.plusInterval, STLInterval.set]
  | nonempty l u lc rc b c _ =>
    simp only [STLInterval.plusInterval]
    by_cases h : J.sup 0 < J.inf 0
    · rw [dif_pos (by simpa using h)]
      simp [STLInterval.set, Set.Icc_eq_empty_of_lt h]
    · rw [dif_neg (by simpa using h), set_stlInterval, STLInterval.toEReal_map_addUp, toReal_real,
        addDown_real, EReal.coe_add, ← rawSet_closed_coe]
      have := rawSet_add (rawSet_nonempty_of_fields b c) (rawSet_closed_nonempty (not_lt.1 h))
      simpa [STLInterval.set] using this

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
