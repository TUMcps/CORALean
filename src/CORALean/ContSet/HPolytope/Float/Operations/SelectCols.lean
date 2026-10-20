module

public import CORALean.ContSet.HPolytope.Float.HPolytope
public import CORALean.ContSet.Interval.Float.Operations.Basic

@[expose] public section

/-!
# `HPolytope.selectCols`

The rows read on the coordinates `sel` only: row `i` becomes `l ↦ Aᵢ (sel l)`, the bounds and
slacks kept. At a point that the rows read through `sel` alone, which is what a coordinate the
rows ignore, or a point that is zero off `sel`, gives, the selected rows read the selected
coordinates as the full rows read the point (`HPolytope.mem_selectCols_nominal_iff`). The error box
is not read and the result's is the origin, as for a constrained zonotope's constraint, which has
none.

## Inputs
* `P` – H-polytope
* `sel` – indices indexed by `Fin k`

## Output
* the rows at the coordinates `sel`, bounds and slacks kept
-/

-- Authors:       Claude Opus 5.5
-- Written:       19-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

variable {𝕋 : Type} [FloatOps 𝕋] {n k : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The rows at the coordinates `sel`, bounds and slacks kept. -/
def HPolytope.selectCols (P : HPolytope 𝕋 (Vec 𝕋 n)) (sel : Fin k → Fin n) :
    HPolytope 𝕋 (Vec 𝕋 k) where
  m := P.m
  A := fun i l => P.A i (sel l)
  b := P.b
  me := P.me
  Ae := fun i l => P.Ae i (sel l)
  be := P.be
  b_error := P.b_error
  be_error := P.be_error
  I_error := Interval.origin k

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
