import CORALean.Global.Float.Instances.Dyadic.Theorems.ToRealNeg
import CORALean.Global.Float.Instances.Flint.Operations.Neg

/-!
# Negation is exact

`Dyadic.toReal_neg` at the same pair: `neg` builds the pair `Dyadic.neg` does.
-/

-- Authors:       Tobias Ladner
-- Written:       28-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float.Flint

variable {p : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem toReal_neg (a : Flint p) : toReal (neg a) = -toReal a :=
  Dyadic.toReal_neg a.toDyadic

end CORALean.Float.Flint


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
