import CORALean.Global.Float.FloatOps

/-!
# Leaky ReLU above a line, at one end

`max (α a) a - m a`, how far leaky ReLU rises above the line of slope `m` at `a`, rounded up.
-/

-- Authors:       Tobias Ladner
-- Written:       01-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Float Float.FloatOps

variable {𝕋 : Type} [FloatOps 𝕋]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `max (α a) a - m a`, rounded up. -/
def leakyReluEndUp (α m a : 𝕋) : 𝕋 := subUp (maximum (mulUp α a) a) (mulDown m a)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
