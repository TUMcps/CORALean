import CORALean.Global.Float.Instances.IEEE.IEEE

/-!
# Negation

Exact: every format is symmetric about zero, so the grid is too.
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

def neg (x : IEEE fmt) : IEEE fmt := ⟨-x.mantissa, x.exponent⟩

end IEEE

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
