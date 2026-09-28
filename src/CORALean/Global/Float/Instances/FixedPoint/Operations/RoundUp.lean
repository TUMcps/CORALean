import CORALean.Global.Float.Instances.FixedPoint.FixedPoint

/-!
# Rounding a mantissa up to `f` digits

At or below `f` digits already, padding with zeros is exact, the same as
`roundDown`. Past `f`, the ceiling is the floor of the negation: negate,
divide, negate back.
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

/-- At or below `f` digits, scaling up is exact; past it, negate, floor-divide, negate back. -/
def roundUp (x : FixedPoint f) : FixedPoint f :=
  if x.d ≤ f then ⟨x.m * 10 ^ (f - x.d), f⟩ else ⟨-(-x.m / 10 ^ (x.d - f)), f⟩

end FixedPoint

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
