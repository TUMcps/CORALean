module

public import CORALean.ContSet.Interval.Float.Operations.Basic

@[expose] public section

/-!
# `Interval.isequal`

The equality test at float: containment each way, by the certified `le`. Certified in one direction
only, so `true` is a proof and `false` is no refutation.

## Inputs
* `I` – first interval box
* `J` – second interval box

## Output
* `true` when each box contains the other
-/

-- Authors:       Claude Opus 5.5
-- Written:       01-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def Interval.isequal (I J : Interval (Vec 𝕋 n)) : Bool := Interval.le I J && Interval.le J I

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
