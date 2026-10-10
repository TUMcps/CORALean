import CORALean.ContSet.Polygon.Float.Operations.Triangulation
import CORALean.ContSet.Conversion.Float.VPolytope_to_PolyZonotope
import CORALean.ContSet.PolyZonotope.Float.Operations.QuadMap
import CORALean.ContSet.PolyZonotope.Float.Operations.Polygon

/-!
# `Polygon.quadMap`, over a floating-point scalar

The float counterpart of `Real.Polygon.quadMap`: the vertex triangles of the float polygon, each
as a float polynomial zonotope through its box, mapped by the float `PolyZonotope.quadMap` (whose
rounded generators are charged to its error box) and enclosed by the float `PolyZonotope.polygon`.
-/

-- Authors:       Tobias Ladner
-- Written:       10-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --
namespace CORALean.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The union of the polygons of the images of the triangles. -/
def Polygon.quadMap (P : Polygon 𝕋) (Q : Fin 2 → Mat 𝕋 2 2) (splits : ℕ)
    (pick : ℕ → PolyZonotope 𝕋 2 → Bool) : Polygon 𝕋 :=
  -- `list = triangulation(pgon)`
  let list : List (VPolytope 𝕋 2) := (Polygon.triangulation P).sets
  -- per triangle `pZ_i_2 = quadMap(polyZonotope(polytope(list{i})), Q)`, then `polygon(pZ_i_2)`
  ⟨list.flatMap fun t => ((PolyZonotope.quadMap Q t.polyZonotope).polygon splits pick).sets⟩

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
