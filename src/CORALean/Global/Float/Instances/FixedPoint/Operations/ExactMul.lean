module

public import CORALean.Global.Float.Instances.FixedPoint.FixedPoint

@[expose] public section

/-!
# The exact product

Closed on fixed-point values: only the mantissa grows and the digit counts
add. `MulUp`/`MulDown` round it back down to `f`.
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

def exactMul (a b : FixedPoint f) : FixedPoint f := ⟨a.m * b.m, a.d + b.d⟩

end FixedPoint

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
