module

public import CORALean.Global.Float.Instances.Binary64.Operations.StepUp

@[expose] public section

/-!
# Addition, rounded up

The machine rounds to nearest, which bounds nothing in a stated direction, so this is the
machine's sum followed by one step outward, `stepUp`: `nextUp` of a round-to-nearest result is
strictly above the exact value, because the exact value is never as far as a whole step from the
nearest float to it. A sum that rounds to zero is exactly zero, subnormals being what make
addition exact near zero, so a zero is kept; a sum outside the normal range is NaN.
-/

-- Authors:       Claude Sonnet 5
-- Written:       22-September-2026
-- Last update:   28-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

namespace Binary64


-- =====================================  MAIN DEFINITION  ====================================== --

def addUp (a b : Float) : Float := stepUp (a + b)

end Binary64

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
