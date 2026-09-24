import CORALean.Global.Float.Instances.Dyadic.Dyadic

/-!
# Halving

Exact: the mantissa is untouched.
-/

-- Authors:       Tobias Ladner
-- Written:       16-August-2026
-- Last update:   02-September-2026
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

namespace Dyadic

variable {p : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- Exact: the mantissa is untouched. -/
def half (a : Dyadic p) : Dyadic p := ⟨a.mantissa, a.exponent - 1⟩

end Dyadic

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
