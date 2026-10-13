module

public import CORALean.Global.Float.Instances.FixedPoint.FixedPoint

@[expose] public section

/-!
# Negation

Exact: flips the mantissa's sign and leaves the digit count alone.
-/

-- Authors:       Claude Opus 5.5
-- Written:       28-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

namespace FixedPoint

variable {f : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def neg (x : FixedPoint f) : FixedPoint f := ⟨-x.m, x.d⟩

end FixedPoint

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
