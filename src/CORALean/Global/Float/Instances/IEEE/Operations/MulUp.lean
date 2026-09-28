import CORALean.Global.Float.Instances.Dyadic.Operations.ExactMul
import CORALean.Global.Float.Instances.IEEE.Operations.RoundUp

/-!
# Multiplication, rounded up

`Dyadic.exactMul`, which loses nothing, then `roundUp` onto the grid of `fmt`.
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

def mulUp (a b : IEEE fmt) : IEEE fmt := roundUp (Dyadic.exactMul a.toDyadic b.toDyadic)

end IEEE

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
