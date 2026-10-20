module

public import CORALean.Specification.STLInterval.Operations.Plus
public import CORALean.Specification.STLInterval.Theorems.SetStlInterval
public import CORALean.Specification.STLInterval.Theorems.RawSetAdd
public import CORALean.Specification.STLInterval.Theorems.Basic

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

open scoped Pointwise


-- =======================================  MAIN THEOREM  ======================================= --

/-- `plus` denotes the sum of the two sets of times. -/
theorem STLInterval.set_plus (I J : STLInterval) :
    (I.plus J).set = I.set + J.set := by -- --- PROOF ---
  cases I with
  | empty => simp [STLInterval.plus, STLInterval.set]
  | nonempty l₁ u₁ lc₁ rc₁ a b c _ =>
    cases J with
    | empty => simp [STLInterval.plus, STLInterval.set]
    | nonempty l₂ u₂ lc₂ rc₂ d e f _ =>
      simp only [STLInterval.plus]
      rw [STLInterval.set_stlInterval]
      exact rawSet_add (rawSet_nonempty_of _ _ _ _ a b c)
        (rawSet_nonempty_of _ _ _ _ d e f)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
