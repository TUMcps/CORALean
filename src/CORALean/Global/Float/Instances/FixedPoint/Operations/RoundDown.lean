module

public import CORALean.Global.Float.Instances.FixedPoint.FixedPoint

@[expose] public section

/-!
# Rounding a mantissa down to `f` digits

At or below `f` digits already, padding with zeros is exact -- there is
nothing to round. Past `f`, integer `/` on ℤ is floor division, so shifting
the mantissa right by the excess digits rounds toward `-∞`, exactly CORA's
"cut off" made sound.

## Inputs
* `x` – fixed-point value

## Output
* the value floored to the format's digit count
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

/-- At or below `f` digits, scaling up is exact; past it, `/` floors. -/
def roundDown (x : FixedPoint f) : FixedPoint f :=
  if x.d ≤ f then ⟨x.m * 10 ^ (f - x.d), f⟩ else ⟨x.m / 10 ^ (x.d - f), f⟩

end FixedPoint

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
