import CORALean.Global.Float.Instances.IEEE.Operations.Le

/-!
# The lesser of two numbers

`le` decides it exactly, so this picks an argument and rounds nothing.
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

def minimum (a b : IEEE fmt) : IEEE fmt := if le a b then a else b

end IEEE

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
