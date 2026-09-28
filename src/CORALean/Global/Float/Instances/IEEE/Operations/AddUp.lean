import CORALean.Global.Float.Instances.Dyadic.Operations.ExactAdd
import CORALean.Global.Float.Instances.IEEE.Operations.RoundUp

/-!
# Addition, rounded up

`Dyadic.exactAdd`, which loses nothing, then `roundUp` onto the grid of `fmt`.
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

def addUp (a b : IEEE fmt) : IEEE fmt := roundUp (Dyadic.exactAdd a.toDyadic b.toDyadic)

end IEEE

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
