module

public import CORALean.Global.Float.Instances.Dyadic.Theorems.LeIff
public import CORALean.Global.Float.Instances.Flint.Operations.Minimum

@[expose] public section

/-!
# `minimum` is exact

`Dyadic.le_iff` at the same pairs picks the smaller side, as it does for
`Dyadic.minimum`.
-/

-- Authors:       Claude Opus 5.5
-- Written:       28-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float.Flint

variable {p : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem toReal_minimum (a b : Flint p) :
    toReal (minimum a b) = min (toReal a) (toReal b) := by
  have hiff : le a b = true ↔ toReal a ≤ toReal b := Dyadic.le_iff a.toDyadic b.toDyadic
  by_cases h : le a b = true
  · rw [minimum, if_pos h, min_eq_left (hiff.mp h)]
  · rw [minimum, if_neg h, min_eq_right (not_le.mp (h ∘ hiff.mpr)).le]

end CORALean.Float.Flint


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
