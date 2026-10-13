import CORALean.ContSet.SetUnion.API
import CORALean.ContSet.VPolytope.Float.API

/-!
# Polygons over a floating-point scalar

The float layer of `Polygon`: a finite union of float polytopes in the plane, each carrying its
own error box, so that nothing is rounded at the union level: every operation hands each piece
to the piece's own float operation. Which sets the representation holds, and what is not
formalized (the conversion from CORA's `polyshape` boundary lists), is as in
`Polygon.Real.Polygon`.
-/

-- Authors:       Tobias Ladner
-- Written:       02-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float


-- =====================================  MAIN DEFINITION  ====================================== --

open FloatOps in
/-- A float polygon: a finite list of float polytopes in the plane, denoting their union. -/
abbrev Polygon (𝕋 : Type) [FloatOps 𝕋] : Type := SetUnion (VPolytope (Vec 𝕋 2))

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
