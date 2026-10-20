module

public import CORALean.Specification.STLInterval.Theorems.RawSetAdd
public import CORALean.Specification.STLInterval.Theorems.RawSetNeg

@[expose] public section

/-!
# The difference of two STL intervals

`I - J` is `I + (-J)`: the difference of nonempty `rawSet`s is `rawSet (l₁-u₂) (u₁-l₂)`, an end
closed when both ends it is made of are.

## Inputs
* `l₁` – lower bound of the first interval
* `u₁` – upper bound of the first interval
* `l₂` – lower bound of the second interval
* `u₂` – upper bound of the second interval
* `lc₁` – first lower bound is closed
* `rc₁` – first upper bound is closed
* `lc₂` – second lower bound is closed
* `rc₂` – second upper bound is closed

## Hypotheses
* `h₁` – the first interval is nonempty
* `h₂` – the second interval is nonempty

## Conclusion
* the difference of the sets has the combined bounds
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open scoped Pointwise


-- =======================================  MAIN THEOREM  ======================================= --

/-- `rawSet (l₁-u₂) (u₁-l₂) (lc₁&&rc₂) (rc₁&&lc₂)` is the difference of two nonempty `rawSet`s. -/
theorem STLInterval.rawSet_sub {l₁ u₁ l₂ u₂ : EReal} {lc₁ rc₁ lc₂ rc₂ : Bool}
    (h₁ : (rawSet l₁ u₁ lc₁ rc₁).Nonempty) (h₂ : (rawSet l₂ u₂ lc₂ rc₂).Nonempty) : -- --- CONCL ---
    rawSet (l₁ - u₂) (u₁ - l₂) (lc₁ && rc₂) (rc₁ && lc₂) =
      rawSet l₁ u₁ lc₁ rc₁ - rawSet l₂ u₂ lc₂ rc₂ := by -- --- PROOF ---
  rw [sub_eq_add_neg (rawSet l₁ u₁ lc₁ rc₁), rawSet_neg]
  have h₂' : (rawSet (-u₂) (-l₂) rc₂ lc₂).Nonempty := by
    rw [← rawSet_neg]; exact h₂.neg
  have := rawSet_add h₁ h₂'
  simpa [sub_eq_add_neg] using this

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
