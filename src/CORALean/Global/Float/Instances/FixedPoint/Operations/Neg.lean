import CORALean.Global.Float.Instances.FixedPoint.FixedPoint

/-!
# Negation

Exact: flips the mantissa's sign and leaves the digit count alone.
-/

-- Authors:       Tobias Ladner
-- Written:       28-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

namespace FixedPoint

variable {f : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def neg (x : FixedPoint f) : FixedPoint f := ⟨-x.m, x.d⟩

end FixedPoint

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
