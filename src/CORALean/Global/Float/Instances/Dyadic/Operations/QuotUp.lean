module

public import CORALean.Global.Float.Instances.Dyadic.Dyadic

@[expose] public section

/-!
# The quotient, rounded up while dividing

`quotDown`'s mirror, at the same shift: negates the shifted dividend twice,
turning the floor into a ceiling exactly as `roundUp` does.
-/

-- Authors:       Claude Sonnet 5
-- Written:       16-August-2026
-- Last update:   25-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

namespace Dyadic

variable {p : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def quotUp (a b : Dyadic p) : Dyadic p :=
  ⟨-(-(a.mantissa * 2 ^ (p + b.mantissa.natAbs.log2 + 1)) / b.mantissa),
    a.exponent - b.exponent - ((p + b.mantissa.natAbs.log2 + 1 : ℕ) : ℤ)⟩

end Dyadic

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
