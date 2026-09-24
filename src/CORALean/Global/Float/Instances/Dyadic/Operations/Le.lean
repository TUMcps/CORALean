import CORALean.Global.Float.Instances.Dyadic.Dyadic

/-!
# Comparison

Exact, and needing no rounding: aligned to the common exponent, the order on
dyadics is the order on their mantissas.
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

def le (a b : Dyadic p) : Bool :=
  a.mantissa * 2 ^ (a.exponent - min a.exponent b.exponent).toNat ≤
    b.mantissa * 2 ^ (b.exponent - min a.exponent b.exponent).toNat

end Dyadic

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
