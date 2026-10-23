module

public import CORALean.Specification.STLInterval.Operations.Plus
public import CORALean.Specification.STLInterval.Theorems.Basic
public import CORALean.Specification.STLInterval.Theorems.RawSetAdd
public import CORALean.Specification.STLInterval.Theorems.RawSetNonemptyOfFields
public import CORALean.Specification.STLInterval.Theorems.SetStlInterval

@[expose] public section

/-!
# `plus` denotes the sum

`I + J` denotes the sum set `{x + y | x ∈ I, y ∈ J}`, empty operands included.

## Inputs
* `I` – first interval
* `J` – second interval

## Hypotheses
* none

## Conclusion
* the sum denotes the sum of the times
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Float FloatOps SoundFloatArithmetic
open scoped Pointwise


-- =======================================  MAIN THEOREM  ======================================= --

/-- `plus` denotes the sum of the two sets of times. -/
theorem STLInterval.set_plus (I J : STLInterval ℝ) : -- --- CONCL ---
    (I.plus J).set = I.set + J.set := by -- --- PROOF ---
  cases I with
  | empty => simp [STLInterval.plus, STLInterval.set]
  | nonempty l₁ u₁ lc₁ rc₁ b c z₁ =>
    cases J with
    | empty => simp [STLInterval.plus, STLInterval.set]
    | nonempty l₂ u₂ lc₂ rc₂ e f z₂ =>
      simp only [STLInterval.plus]
      rw [STLInterval.set_stlInterval, STLInterval.toEReal_addUpTop]
      -- the sum of the lower bounds is `≥ 0`, so nothing is cut
      have hlb : toReal (maximum zero (addDown l₁ l₂)) = l₁ + l₂ := by
        simp only [toReal_real] at z₁ z₂
        simp [add_nonneg z₁ z₂]
      rw [hlb, EReal.coe_add]
      exact rawSet_add (rawSet_nonempty_of_fields b c) (rawSet_nonempty_of_fields e f)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
