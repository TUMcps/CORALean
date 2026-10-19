module

public import CORALean.ContSet.VPolytope.Float.VPolytope
public import CORALean.ContSet.Interval.Float.Operations.Basic

@[expose] public section

/-!
# `VPolytope.enclosePoints`

CORA's `enclosePoints`: the polytope spanned by a list of points, the points as the vertex list.
The points are stored floats, so the hull of them is exact and the error box is the origin.

## Inputs
* `N` – number of points
* `pts` – points

## Output
* polytope with the points as vertices
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The points are the family `pts`, as the exact layer's are. -/
def VPolytope.enclosePoints {N : ℕ} (pts : Fin N → Vec 𝕋 n) : VPolytope (Vec 𝕋 n) :=
  ⟨N, pts, Interval.origin n⟩

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
