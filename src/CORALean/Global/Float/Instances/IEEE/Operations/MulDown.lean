import CORALean.Global.Float.Instances.Dyadic.Operations.ExactMul
import CORALean.Global.Float.Instances.IEEE.Operations.RoundDown

/-!
# Multiplication, rounded down

`Dyadic.exactMul`, which loses nothing, then `roundDown` onto the grid of `fmt`.
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

def mulDown (a b : IEEE fmt) : IEEE fmt := roundDown (Dyadic.exactMul a.toDyadic b.toDyadic)

end IEEE

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
