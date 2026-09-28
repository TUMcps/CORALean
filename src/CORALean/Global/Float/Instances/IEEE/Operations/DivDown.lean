import CORALean.Global.Float.Instances.Dyadic.Operations.DivDown
import CORALean.Global.Float.Instances.IEEE.Operations.RoundDown

/-!
# Division, rounded down

`DivUp`'s mirror: `Dyadic.divDown` to `p` bits, then `roundDown` onto the grid.
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

def divDown (a b : IEEE fmt) : IEEE fmt := roundDown (Dyadic.divDown a.toDyadic b.toDyadic)

end IEEE

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
