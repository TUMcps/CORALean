module

public import CORALean.ContSet.Polygon.Real.Polygon

@[expose] public section

/-!
# `ContSet/Polygon/Real/Operations`: small declarations

One section per declaration, at most five code lines each; alphabetical, after the
sections each one uses (CONTRIBUTING, "Small declarations").
-/


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --


-- =====================================  `Polygon.empty`  ====================================== --
-- Authors:       Claude Opus 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---

namespace CORALean.Real

/-- The empty polygon, `polygon(zeros(2,0))`.

CORA's `polygon.empty`: no pieces. -/
def Polygon.empty : Polygon := ⟨[]⟩

end CORALean.Real


-- =======================================  `Polygon.or`  ======================================= --
-- Authors:       Claude Opus 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---

namespace CORALean.Real

/-- The union: the pieces of both.

CORA's `polygon/or`: the union, whose pieces are those of both. -/
def Polygon.or (P Q : Polygon) : Polygon := ⟨P.sets ++ Q.sets⟩

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
