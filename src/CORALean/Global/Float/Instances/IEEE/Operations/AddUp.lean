module

public import CORALean.Global.Float.Instances.Dyadic.Operations.ExactAdd
public import CORALean.Global.Float.Instances.IEEE.Operations.RoundUp

@[expose] public section

/-!
# Addition, rounded up

`Dyadic.exactAdd`, which loses nothing, then `roundUp` onto the grid of `fmt`.

## Inputs
* `a` – first addend
* `b` – second addend

## Output
* the exact sum rounded up onto the format's grid
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

def addUp (a b : IEEE fmt) : IEEE fmt := roundUp (Dyadic.exactAdd a.toDyadic b.toDyadic)

end IEEE

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
