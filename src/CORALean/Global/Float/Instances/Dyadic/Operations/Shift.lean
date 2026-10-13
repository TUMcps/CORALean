import CORALean.Global.Float.Instances.Dyadic.Dyadic

/-!
# How far a mantissa exceeds `p` bits

What `roundUp`/`roundDown` drop from the mantissa to bring it back to `p`
bits.
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

def shift (d : Dyadic p) : ℕ := Nat.log2 d.mantissa.natAbs + 1 - p

end Dyadic

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
