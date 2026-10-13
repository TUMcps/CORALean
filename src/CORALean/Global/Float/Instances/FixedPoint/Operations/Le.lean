import CORALean.Global.Float.Instances.FixedPoint.FixedPoint

/-!
# Comparison

Exact, and needing no rounding: cross-multiplied by the other side's power of
ten, two values at different digit counts compare the same way their exact
rationals do, with nothing to align first.
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

def le (a b : FixedPoint f) : Bool := a.m * 10 ^ b.d ≤ b.m * 10 ^ a.d

end FixedPoint

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
