module

public import CORALean.Global.Float.Instances.Dyadic.Operations.Basic
public import CORALean.Global.Float.Instances.Dyadic.Theorems.CoarsenDownLe
public import CORALean.Global.Float.Instances.Dyadic.Theorems.RoundDownLe
public import CORALean.Global.Float.Instances.Dyadic.Theorems.ToRealExactAdd

@[expose] public section

/-!
# The downward sum is bounded by the real sum

`addDown` coarsens both operands downward, adds exactly, and rounds down; each step only lowers
the value (`coarsenDown_le`, `toReal_exactAdd`, `roundDown_le`).
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       10-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float.Dyadic

variable {p : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem addDown_le_add (a b : Dyadic p) : toReal (addDown a b) ≤ toReal a + toReal b := by
  rw [addDown]
  refine le_trans (roundDown_le _) ?_
  rw [toReal_exactAdd]
  exact add_le_add (coarsenDown_le _ a) (coarsenDown_le _ b)

end CORALean.Float.Dyadic


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
