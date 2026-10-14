module

public import CORALean.Global.Float.Instances.Dyadic.Theorems.LeIff
public import CORALean.Global.Float.Instances.Flint.Operations.Basic

@[expose] public section

/-!
# `maximum` is exact

`Dyadic.le_iff` at the same pairs picks the larger side, as it does for
`Dyadic.maximum`.
-/

-- Authors:       Claude Opus 5.5
-- Written:       28-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float.Flint

variable {p : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem toReal_maximum (a b : Flint p) :
    toReal (maximum a b) = max (toReal a) (toReal b) := by
  have hiff : le a b = true ↔ toReal a ≤ toReal b := Dyadic.le_iff a.toDyadic b.toDyadic
  by_cases h : le a b = true
  · rw [maximum, if_pos h, max_eq_right (hiff.mp h)]
  · rw [maximum, if_neg h, max_eq_left (not_le.mp (h ∘ hiff.mpr)).le]

end CORALean.Float.Flint


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
