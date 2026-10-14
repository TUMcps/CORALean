module

public import CORALean.ContSet.Polygon.Real.Polygon
public import CORALean.ContSet.VPolytope.Real.Operations.Basic

@[expose] public section

/-!
# `Polygon.project`

CORA's `polygon/project` at two coordinates, `V(dims,:)`, and `projectHighDim_`/`lift_` at `N =
2`, which CORA reduces to it. Every piece is projected. With one coordinate CORA projects the
interval hull instead; that case is `Polygon.interval` followed by `Interval.project`, not given
here.
-/

-- Authors:       Claude Opus 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =====================================  MAIN DEFINITION  ====================================== --

/-- Every piece read at the coordinates `dims`. -/
def Polygon.project (P : Polygon) (dims : Fin 2 → Fin 2) : Polygon :=
  ⟨P.sets.map fun p => VPolytope.project p dims⟩

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
