import CORALean.Global.Float.Instances.IEEE.IEEE

/-!
# Halving

Exact, as the class demands, because only the exponent moves. Below the normal range that is a
step finer than the format has: the halved smallest subnormal is no number of `fmt`. The result
is kept exactly, and the next rounded operation rounds it back onto the grid.
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

/-- Exact, and off the grid when `x` is subnormal. -/
def half (x : IEEE fmt) : IEEE fmt := ⟨x.mantissa, x.exponent - 1⟩

end IEEE

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
