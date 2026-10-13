module

public import CORALean.Global.Float.Instances.Dyadic.Operations.Le
public import CORALean.Global.Float.Instances.IEEE.IEEE

@[expose] public section

/-!
# Comparison

Exact: `Dyadic.le`, which compares the mantissas at the common exponent.
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

def le (a b : IEEE fmt) : Bool := Dyadic.le a.toDyadic b.toDyadic

end IEEE

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
