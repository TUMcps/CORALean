import CORALean.Global.Float.Instances.Binary64.Operations.NextUp

/-!
# Division, rounded up

The machine's quotient, nudged one step out by `nextUp` — see `AddUp` for why
that suffices whatever the machine's own rounding did.
-/

-- Authors:       Tobias Ladner
-- Written:       22-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

namespace Binary64


-- =====================================  MAIN DEFINITION  ====================================== --

def divUp (a b : Float) : Float := nextUp (a / b)

end Binary64

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
