import CORALean.Global.Float.Instances.IEEE.Operations.Le

/-!
# The greater of two numbers

`le` decides it exactly, so this picks an argument and rounds nothing.
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

def maximum (a b : IEEE fmt) : IEEE fmt := if le a b then b else a

end IEEE

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
