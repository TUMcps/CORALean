import CORALean.Global.Float.Instances.Dyadic.Operations.Shift

/-!
# Rounding a mantissa down to `p` bits

Integer `/` is floor division on ℤ, so shifting the mantissa right by `shift`
bits and raising the exponent to match rounds toward `-∞`.
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

def roundDown (d : Dyadic p) : Dyadic p :=
  ⟨d.mantissa / 2 ^ d.shift, d.exponent + d.shift⟩

end Dyadic

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
