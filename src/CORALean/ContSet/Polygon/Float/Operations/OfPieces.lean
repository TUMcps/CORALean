import CORALean.ContSet.Polygon.Float.Polygon

/-!
# `Polygon.ofPieces`, over a floating-point scalar

The constructor: a polygon from float convex pieces.
-/

-- Authors:       Tobias Ladner
-- Written:       02-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The union of the float convex pieces `pieces`. -/
def Polygon.ofPieces (pieces : List (VPolytope 𝕋 2)) : Polygon 𝕋 := ⟨pieces⟩

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
