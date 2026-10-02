import CORALean.ContSet.ConZonotope.Float.ConZonotope
import CORALean.ContSet.Interval.Float.Operations.Origin
import CORALean.ContSet.HPolytope.Float.Operations.Fullspace

/-!
# `ConZonotope.origin`, over a floating-point scalar

The point `0` as a constrained zonotope with no generators and no constraints, the
centre stored as `zero` and the error box at zero.
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

def ConZonotope.origin (n : ℕ) : ConZonotope 𝕋 n where
  h := 0
  c := fun _ => zero
  G := fun _ j => j.elim0
  P := HPolytope.fullspace 𝕋 0
  E := Interval.origin n

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
