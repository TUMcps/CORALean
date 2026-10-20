module

public import CORALean.Global.Float.Instances.FixedPoint.Operations.Basic
public import CORALean.Global.Float.Instances.FixedPoint.Theorems.LeIff

@[expose] public section

/-!
# `minimum` is exact

`le_iff` picks the smaller side directly, which is what lets `minimum` absorb
a sign without widening anything. What `SoundFloatArithmetic.toReal_minimum`
needs from `FixedPoint`.

## Inputs
* `a` – first value
* `b` – second value

## Hypotheses
* none

## Conclusion
* the minimum denotes the smaller of the two real values
-/

-- Authors:       Claude Opus 5.5
-- Written:       28-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float.FixedPoint

variable {f : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem toReal_minimum (a b : FixedPoint f) :
    toReal (minimum a b) = min (toReal a) (toReal b) := by
  by_cases h : le a b = true
  · rw [minimum, if_pos h, min_eq_left ((le_iff a b).mp h)]
  · rw [minimum, if_neg h, min_eq_right (not_le.mp (h ∘ (le_iff a b).mpr)).le]

end CORALean.Float.FixedPoint


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
