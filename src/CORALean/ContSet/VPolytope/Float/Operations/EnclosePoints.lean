import CORALean.ContSet.VPolytope.Float.VPolytope
import CORALean.ContSet.Interval.Float.Operations.Origin

/-!
# `VPolytope.enclosePoints`

CORA's `enclosePoints`: the polytope spanned by a list of points, the points as the vertex list.
The points are stored floats, so the hull of them is exact and the error box is the origin.
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

/-- The points are the columns of `pts`. -/
def VPolytope.enclosePoints {N : ℕ} (pts : Mat 𝕋 n N) : VPolytope 𝕋 n :=
  ⟨N, pts, Interval.origin n⟩

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
