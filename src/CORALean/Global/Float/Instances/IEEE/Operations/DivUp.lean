import CORALean.Global.Float.Instances.Dyadic.Operations.DivUp
import CORALean.Global.Float.Instances.IEEE.Operations.RoundUp

/-!
# Division, rounded up

A quotient is not dyadic, so there is no exact step: `Dyadic.divUp` rounds up to `p` bits at an
unbounded exponent, and `roundUp` onto the grid. Both round the same way, so the bound composes;
the unit checks in `Examples/IEEERounding.lean` compare the result with binary64's own.
-/

-- Authors:       Tobias Ladner
-- Written:       28-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

namespace IEEE

variable {fmt : IEEEFormat}


-- =====================================  MAIN DEFINITION  ====================================== --

def divUp (a b : IEEE fmt) : IEEE fmt := roundUp (Dyadic.divUp a.toDyadic b.toDyadic)

end IEEE

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
