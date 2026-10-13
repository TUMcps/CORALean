import CORALean.ContSet.Polygon.Real.Polygon

/-!
# `Polygon.or`

CORA's `polygon/or`: the union, whose pieces are those of both.
-/

-- Authors:       Claude Opus 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The union: the pieces of both. -/
def Polygon.or (P Q : Polygon) : Polygon := ⟨P.sets ++ Q.sets⟩

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
