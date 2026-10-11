import CORALean.Global.Float.Instances.Dyadic.Operations.AddUp
import CORALean.Global.Float.Instances.Dyadic.Operations.AlignExp
import CORALean.Global.Float.Instances.Dyadic.Theorems.LeCoarsenUp
import CORALean.Global.Float.Instances.Dyadic.Theorems.LeRoundUp
import CORALean.Global.Float.Instances.Dyadic.Theorems.ToRealExactAdd

/-!
# The upward sum bounds the real sum

`addUp` coarsens both operands upward, adds exactly, and rounds up; each step only raises the
value (`le_coarsenUp`, `toReal_exactAdd`, `le_roundUp`).
-/

-- Authors:       Tobias Ladner
-- Written:       10-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float.Dyadic

variable {p : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem add_le_addUp (a b : Dyadic p) : toReal a + toReal b ≤ toReal (addUp a b) := by
  rw [addUp]
  refine le_trans ?_ (le_roundUp _)
  rw [toReal_exactAdd]
  exact add_le_add (le_coarsenUp _ a) (le_coarsenUp _ b)

end CORALean.Float.Dyadic


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
