module

public import CORALean.Specification.STLInterval.Operations.Minus
public import CORALean.Specification.STLInterval.Theorems.SetStlInterval
public import CORALean.Specification.STLInterval.Theorems.RawSetSub
public import CORALean.Specification.STLInterval.Theorems.RawSetClamp
public import CORALean.Specification.STLInterval.Theorems.Basic

@[expose] public section

/-!
# `minus` denotes the nonnegative differences

`I - J` denotes `{x - y | x ∈ I, y ∈ J}` met with `[0, ∞)`: a negative lower bound is cut to `0`.

## Inputs
* `I` – first interval
* `J` – second interval

## Hypotheses
* none

## Conclusion
* the difference denotes the nonnegative differences of the times
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open scoped Pointwise


-- =======================================  MAIN THEOREM  ======================================= --

/-- `minus` denotes the differences of the two sets, at least `0`. -/
theorem STLInterval.set_minus (I J : STLInterval) : -- --- CONCL ---
    (I.minus J).set = (I.set - J.set) ∩ Set.Ici 0 := by -- --- PROOF ---
  cases I with
  | empty => simp [STLInterval.minus, STLInterval.set]
  | nonempty l₁ u₁ lc₁ rc₁ a b c _ =>
    cases J with
    | empty => simp [STLInterval.minus, STLInterval.set]
    | nonempty l₂ u₂ lc₂ rc₂ d e f _ =>
      simp only [STLInterval.minus]
      have h := rawSet_sub (rawSet_nonempty_of _ _ _ _ a b c)
        (rawSet_nonempty_of _ _ _ _ d e f)
      show _ = (rawSet l₁ u₁ lc₁ rc₁ - rawSet l₂ u₂ lc₂ rc₂) ∩ Set.Ici 0
      rw [← h, rawSet_clamp]
      split_ifs <;> exact set_stlInterval _ _ _ _ _

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
