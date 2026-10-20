module

public import CORALean.Global.Float.Instances.Dyadic.Operations.Basic
public import CORALean.Global.Float.Instances.IEEE.Operations.RoundUp

@[expose] public section

/-!
# Division, rounded up

A quotient is not dyadic, so there is no exact step: `Dyadic.divUp` rounds up to `p` bits at an
unbounded exponent, and `roundUp` onto the grid. Both round the same way, so the bound composes;
the unit checks in `Examples/IEEERounding.lean` compare the result with binary64's own.

## Inputs
* `a` – dividend
* `b` – divisor

## Output
* the quotient rounded up onto the format's grid
-/

-- Authors:       Claude Opus 5.5
-- Written:       28-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

namespace IEEE

variable {fmt : IEEEFormat}


-- =====================================  MAIN DEFINITION  ====================================== --

def divUp (a b : IEEE fmt) : IEEE fmt := roundUp (Dyadic.divUp a.toDyadic b.toDyadic)

end IEEE

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
