import CORALean.ContSet.VPolytope.Float.VPolytope
import CORALean.ContSet.Interval.Float.Operations.Origin

/-!
# `VPolytope.origin`, over a floating-point scalar

CORA's `polytope.origin(n)` in its vertex form: the single vertex `0`, stored as `zero`, and
the error box at the point `0`.
-/

-- Authors:       Tobias Ladner
-- Written:       02-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋]


-- =====================================  MAIN DEFINITION  ====================================== --

def VPolytope.origin (n : ℕ) : VPolytope 𝕋 n where
  k := 1
  V := fun _ _ => zero
  E := Interval.origin n

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
