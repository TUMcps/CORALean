import CORALean.Global.Float.Instances.Dyadic.Dyadic

/-!
# The quotient, rounded up while dividing

`quotDown`'s mirror: negates the shifted dividend twice, turning the floor
into a ceiling exactly as `roundUp` does.
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

def quotUp (a b : Dyadic p) : Dyadic p :=
  ⟨-(-(a.mantissa * 2 ^ p) / b.mantissa), a.exponent - b.exponent - p⟩

end Dyadic

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
