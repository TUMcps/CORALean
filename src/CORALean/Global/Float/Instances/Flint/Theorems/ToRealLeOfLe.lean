import CORALean.Global.Float.Instances.Dyadic.Theorems.ToRealLeOfLe
import CORALean.Global.Float.Instances.Flint.Operations.Le

/-!
# `le` only approves what is true

`le` is `Dyadic.le` of the same pairs, so this is `Dyadic.toReal_le_of_le`.
-/

-- Authors:       Claude Opus 5.5
-- Written:       28-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float.Flint

variable {p : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem toReal_le_of_le {a b : Flint p} (h : le a b = true) : toReal a ≤ toReal b :=
  Dyadic.toReal_le_of_le h

end CORALean.Float.Flint


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
