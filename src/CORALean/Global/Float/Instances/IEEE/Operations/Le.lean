import CORALean.Global.Float.Instances.Dyadic.Operations.Le
import CORALean.Global.Float.Instances.IEEE.IEEE

/-!
# Comparison

Exact: `Dyadic.le`, which compares the mantissas at the common exponent.
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

def le (a b : IEEE fmt) : Bool := Dyadic.le a.toDyadic b.toDyadic

end IEEE

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
