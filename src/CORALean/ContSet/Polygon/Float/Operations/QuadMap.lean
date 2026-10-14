module

public import CORALean.ContSet.Polygon.Float.Operations.Triangulation
public import CORALean.ContSet.Conversion.Float.Operations.Basic
public import CORALean.ContSet.PolyZonotope.Float.Operations.QuadMap
public import CORALean.ContSet.PolyZonotope.Float.Operations.Polygon
public import CORALean.ContSet.Conversion.Float.Operations.ConPolyZono_to_PolyZonotope
public import CORALean.ContSet.Conversion.Float.Operations.Zonotope_to_PolyZonotope

@[expose] public section

/-!
# `Polygon.quadMap`, over a floating-point scalar

The float counterpart of `Real.Polygon.quadMap`: the vertex triangles of the float polygon, each
as a float polynomial zonotope through its box, mapped by the float `PolyZonotope.quadMap` (whose
rounded generators are charged to its error box) and enclosed by the float `PolyZonotope.polygon`.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       10-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --
namespace CORALean.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The union of the polygons of the images of the triangles. -/
def Polygon.quadMap (P : Polygon 𝕋) (Q : Fin 2 → Mat 𝕋 2 2) (splits : ℕ)
    (pick : ℕ → PolyZonotope (Vec 𝕋 2) → Bool) : Polygon 𝕋 :=
  -- `list = triangulation(pgon)`
  let list : List (VPolytope (Vec 𝕋 2)) := (Polygon.triangulation P).sets
  -- per triangle `pZ_i_2 = quadMap(polyZonotope(polytope(list{i})), Q)`, then `polygon(pZ_i_2)`
  ⟨list.flatMap fun t => ((PolyZonotope.quadMap Q t.polyZonotope).polygon splits pick).sets⟩

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
