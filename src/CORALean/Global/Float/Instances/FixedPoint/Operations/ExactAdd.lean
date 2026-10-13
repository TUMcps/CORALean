module

public import CORALean.Global.Float.Instances.FixedPoint.FixedPoint

@[expose] public section

/-!
# The exact sum

Cross-multiplied to a common digit count `a.d + b.d`, the way two rationals
with different denominators always add -- closed on fixed-point values, so
this loses nothing. `AddUp`/`AddDown` round it back to `f` digits.
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

/-- Cross-multiplied to `a.d + b.d` digits -- a common digit count, the way two
rationals with different denominators always add. -/
def exactAdd (a b : FixedPoint f) : FixedPoint f := ⟨a.m * 10 ^ b.d + b.m * 10 ^ a.d, a.d + b.d⟩

end FixedPoint

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
