module

public import CORALean.Global.Float.Instances.Dyadic.Operations.Basic
public import CORALean.Global.Float.Instances.Dyadic.Theorems.LeCoarsenUp
public import CORALean.Global.Float.Instances.Dyadic.Theorems.LeRoundUp
public import CORALean.Global.Float.Instances.Dyadic.Theorems.ToRealExactAdd

@[expose] public section

/-!
# The upward sum bounds the real sum

`addUp` coarsens both operands upward, adds exactly, and rounds up; each step only raises the
value (`le_coarsenUp`, `toReal_exactAdd`, `le_roundUp`).
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       10-October-2026
-- Last update:   ---
-- Reviewed:      ---


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
