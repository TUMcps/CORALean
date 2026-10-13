import CORALean.ContSet.Polygon.Real.Polygon

/-!
# `Polygon.empty`

CORA's `polygon.empty`: no pieces.
-/

-- Authors:       Claude Opus 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The empty polygon, `polygon(zeros(2,0))`. -/
def Polygon.empty : Polygon := ⟨[]⟩

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
