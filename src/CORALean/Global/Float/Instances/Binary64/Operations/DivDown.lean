module

public import CORALean.Global.Float.Instances.Binary64.Operations.DivUp

@[expose] public section

/-!
# Division, rounded down

The dividend is what gets negated, so the divisor stays positive and the
assumed bound applies unchanged — which is why this mirrors `a` and not `b`,
and why `Theorems` needs the same hypothesis on the divisor that `div_le_divUp`
carries and no more.

## Inputs
* `a` – dividend
* `b` – divisor

## Output
* the quotient rounded down, the negation of the upward quotient of the negated dividend
-/

-- Authors:       Claude Sonnet 5
-- Written:       22-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

namespace Binary64


-- =====================================  MAIN DEFINITION  ====================================== --

def divDown (a b : Float) : Float := -divUp (-a) b

end Binary64

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
