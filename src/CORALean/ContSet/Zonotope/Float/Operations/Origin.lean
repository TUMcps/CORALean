import CORALean.ContSet.Zonotope.Float.Operations.Point

/-!
# `Zonotope.origin`, over a floating-point scalar

The point `0` as a zonotope with no generators, the centre stored as `zero`
and the error box at zero, as `Interval.origin` is for a box.
-/

-- Authors:       Tobias Ladner
-- Written:       02-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def Zonotope.origin (n : ℕ) : Zonotope (Vec 𝕋 n) := Zonotope.point fun _ => zero

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
