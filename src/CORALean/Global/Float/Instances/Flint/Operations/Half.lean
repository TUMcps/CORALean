import CORALean.Global.Float.Instances.Flint.Flint

/-!
# Halving

Exact and pure Lean: the exponent drops by one and the mantissa is untouched,
as in `Dyadic.half`.
-/

-- Authors:       Tobias Ladner
-- Written:       28-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

namespace Flint

variable {p : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def half (a : Flint p) : Flint p := ⟨a.mantissa, a.exponent - 1⟩

end Flint

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
