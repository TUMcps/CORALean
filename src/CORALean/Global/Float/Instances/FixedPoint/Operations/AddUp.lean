module

public import CORALean.Global.Float.Instances.FixedPoint.Operations.ExactAdd
public import CORALean.Global.Float.Instances.FixedPoint.Operations.RoundUp

@[expose] public section

/-!
# Addition, rounded up

`exactAdd`, then `roundUp` back to `f` digits.
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

def addUp (a b : FixedPoint f) : FixedPoint f := roundUp (exactAdd a b)

end FixedPoint

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
