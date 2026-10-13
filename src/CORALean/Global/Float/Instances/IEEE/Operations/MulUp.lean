module

public import CORALean.Global.Float.Instances.Dyadic.Operations.ExactMul
public import CORALean.Global.Float.Instances.IEEE.Operations.RoundUp

@[expose] public section

/-!
# Multiplication, rounded up

`Dyadic.exactMul`, which loses nothing, then `roundUp` onto the grid of `fmt`.
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

def mulUp (a b : IEEE fmt) : IEEE fmt := roundUp (Dyadic.exactMul a.toDyadic b.toDyadic)

end IEEE

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
