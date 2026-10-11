import CORALean.Global.Float.Instances.Dyadic.Operations.AddDown
import CORALean.Global.Float.Instances.Dyadic.Operations.AlignExp
import CORALean.Global.Float.Instances.Dyadic.Theorems.CoarsenDownLe
import CORALean.Global.Float.Instances.Dyadic.Theorems.RoundDownLe
import CORALean.Global.Float.Instances.Dyadic.Theorems.ToRealExactAdd

/-!
# The downward sum is bounded by the real sum

`addDown` coarsens both operands downward, adds exactly, and rounds down; each step only lowers
the value (`coarsenDown_le`, `toReal_exactAdd`, `roundDown_le`).
-/

-- Authors:       Tobias Ladner
-- Written:       10-October-2026
-- Last update:   ---
-- Last revision: ---


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
