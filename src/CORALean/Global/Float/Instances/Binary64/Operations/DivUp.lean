import CORALean.Global.Float.Instances.Binary64.Operations.StepUp

/-!
# Division, rounded up

The machine's quotient, nudged one step out by `stepUp` — see `AddUp` for why that suffices
whatever the machine's own rounding did. A nonzero dividend whose quotient rounds to zero has
underflowed, so that is NaN, as `MulUp`'s underflow is.
-/

-- Authors:       Claude Sonnet 5
-- Written:       22-September-2026
-- Last update:   28-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

namespace Binary64


-- =====================================  MAIN DEFINITION  ====================================== --

def divUp (a b : Float) : Float :=
  let r := a / b
  -- `0` and NaN by their bits, see `inRange`
  if r == Float.ofBits 0 && a != Float.ofBits 0 then Float.ofBits 0x7FF8000000000000
  else stepUp r

end Binary64

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
