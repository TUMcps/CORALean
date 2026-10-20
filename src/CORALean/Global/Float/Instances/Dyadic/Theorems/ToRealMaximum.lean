module

public import CORALean.Global.Float.Instances.Dyadic.Operations.Maximum
public import CORALean.Global.Float.Instances.Dyadic.Theorems.LeIff

@[expose] public section

/-!
# `maximum` is exact

`le_iff` picks the larger side directly, which is what lets `maximum` absorb
a sign without widening anything. What `SoundFloatArithmetic.toReal_maximum`
needs from `Dyadic`.

## Inputs
* `a` – first dyadic
* `b` – second dyadic

## Hypotheses
* none

## Conclusion
* the maximum denotes the larger of the two real values
-/

-- Authors:       Claude Opus 5
-- Written:       16-August-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float.Dyadic

variable {p : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem toReal_maximum (a b : Dyadic p) :
    toReal (maximum a b) = max (toReal a) (toReal b) := by
  by_cases h : le a b = true
  · rw [maximum, if_pos h, max_eq_right ((le_iff a b).mp h)]
  · rw [maximum, if_neg h, max_eq_left (not_le.mp (h ∘ (le_iff a b).mpr)).le]

end CORALean.Float.Dyadic


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
