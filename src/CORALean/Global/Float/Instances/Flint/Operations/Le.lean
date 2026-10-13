import CORALean.Global.Float.Instances.Dyadic.Operations.Le
import CORALean.Global.Float.Instances.Flint.Flint

/-!
# Comparison

Exact and pure Lean: `Dyadic.le` of the same pairs, which aligns the two to
their common exponent and compares integers.
-/

-- Authors:       Claude Opus 5.5
-- Written:       28-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

namespace Flint

variable {p : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def le (a b : Flint p) : Bool := Dyadic.le a.toDyadic b.toDyadic

end Flint

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
