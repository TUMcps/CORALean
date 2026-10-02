import CORALean.ContSet.Polygon.Real.Polygon

/-!
# `Polygon.or`

CORA's `polygon/or`: the union, whose pieces are those of both.
-/

-- Authors:       Tobias Ladner
-- Written:       02-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The union: the pieces of both. -/
def Polygon.or (P Q : Polygon) : Polygon := ⟨P.sets ++ Q.sets⟩

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
