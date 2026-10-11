import CORALean.Global.Float.Instances.Dyadic.Operations.LeShl
import CORALean.Global.Float.Instances.Dyadic.Operations.LeShr

/-!
# Comparison

Exact, and needing no rounding: aligned to the common exponent, the order on dyadics is the order
on their mantissas. When the exponents are so far apart that the aligned mantissa dwarfs the
other one, the sign alone decides (`leShl`, `leShr`), and the alignment is not formed.
-/

-- Authors:       Tobias Ladner
-- Written:       16-August-2026
-- Last update:   10-October-2026
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

namespace Dyadic

variable {p : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def le (a b : Dyadic p) : Bool :=
  if a.exponent ≤ b.exponent then leShl a.mantissa b.mantissa (b.exponent - a.exponent).toNat
  else leShr a.mantissa b.mantissa (a.exponent - b.exponent).toNat

end Dyadic

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
