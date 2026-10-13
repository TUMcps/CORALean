module

public import CORALean.Global.Float.Instances.Dyadic.Operations.LeShl

@[expose] public section

/-!
# `m * 2 ^ g ≤ n` without the power

The mirror image of `leShl`, by negating both sides.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       10-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

namespace Dyadic

variable {p : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def leShr (m n : ℤ) (g : ℕ) : Bool := leShl (-n) (-m) g

end Dyadic

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
