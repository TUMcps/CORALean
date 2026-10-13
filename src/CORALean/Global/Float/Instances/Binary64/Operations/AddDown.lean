module

public import CORALean.Global.Float.Instances.Binary64.Operations.AddUp

@[expose] public section

/-!
# Addition, rounded down

Negation flips the sign bit and nothing else, so this rounds down by rounding
its negation up. Definitional, so the guarantee in `Theorems` is the upward
assumption read through `toReal_neg`, needing no axiom of its own.
-/

-- Authors:       Claude Sonnet 5
-- Written:       22-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

namespace Binary64


-- =====================================  MAIN DEFINITION  ====================================== --

def addDown (a b : Float) : Float := -addUp (-a) (-b)

end Binary64

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
