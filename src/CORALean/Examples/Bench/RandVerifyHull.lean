import CORALean.ContSet.Zonotope.Float.Operations.Mtimes
import CORALean.ContSet.Conversion.Float.Zonotope_to_Interval
import CORALean.Examples.Bench.RandVerifySystem

/-!
# `randverify`: windows in output space, as boxes

`Y = C · R` with the library's own `Zonotope.mtimes` (rounding paid into the error box), then
the interval hull `Zonotope.interval`, each end rounded away from the set. The hull is the
support function of `Y` along `±e_i`, and `±e_i` are the facet normals of an unsafe set that is
a box, so for box unsafe sets the hull loses nothing a support bound along the facet normals
would keep.
-/

-- Authors:       Tobias Ladner
-- Written:       01-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Bench

open CORALean CORALean.Float

variable {𝕋 : Type} [FloatOps 𝕋]


-- =====================================  MAIN DEFINITION  ====================================== --

def outputHulls (C : Mat 𝕋 2 5) (Rs : List (Zonotope (Vec 𝕋 5))) : List (Interval (Vec 𝕋 2)) :=
  Rs.map fun R => (Zonotope.mtimes C R).interval

end CORALean.Bench


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
