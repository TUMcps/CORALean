import CORALean.Global.Float.Instances.Dyadic.Dyadic

/-!
# Negation

Exact: flips the mantissa's sign and leaves the exponent alone.
-/

-- Authors:       Claude Sonnet 5
-- Written:       16-August-2026
-- Last update:   02-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

namespace Dyadic

variable {p : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def neg (d : Dyadic p) : Dyadic p := ⟨-d.mantissa, d.exponent⟩

end Dyadic

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
