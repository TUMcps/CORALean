module

public import CORALean.Specification.STLInterval.Operations.Basic
public import CORALean.Specification.STLInterval.Definitions.Fields
public import Mathlib.Data.EReal.Operations

@[expose] public section

/-!
# The lower bound is nonnegative

If the lower bound of an interval is `≥ 0`, so is the real `lowerBound`.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean


-- =======================================  MAIN THEOREM  ======================================= --

theorem STLInterval.zero_le_lowerBound (I : STLInterval)
    (hI : ∀ f, I.fieldsOf = some f → 0 ≤ f.lower) : 0 ≤ I.lowerBound := by
  cases I with
  | empty => exact le_rfl
  | nonempty l u lc rc h1 h2 h3 => exact EReal.toReal_nonneg (hI _ rfl)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
