import CORALean.Global.Float.Instances.Dyadic.Theorems.ToRealHalf
import CORALean.Global.Float.Instances.Flint.Operations.Half

/-!
# Halving is exact

`Dyadic.toReal_half` at the same pair: `half` builds the pair `Dyadic.half`
does.
-/

-- Authors:       Tobias Ladner
-- Written:       28-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float.Flint

variable {p : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem toReal_half (a : Flint p) : toReal (half a) = toReal a / 2 :=
  Dyadic.toReal_half a.toDyadic

end CORALean.Float.Flint


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
