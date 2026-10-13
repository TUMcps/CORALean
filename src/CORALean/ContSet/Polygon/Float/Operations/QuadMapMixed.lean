import CORALean.ContSet.Polygon.Float.Operations.Triangulation
import CORALean.ContSet.Conversion.Float.VPolytope_to_PolyZonotope
import CORALean.ContSet.PolyZonotope.Float.Operations.QuadMapMixed
import CORALean.ContSet.PolyZonotope.Float.Operations.Polygon

/-!
# `Polygon.quadMapMixed`, over a floating-point scalar

The float counterpart of `Real.Polygon.quadMapMixed`: every pair of vertex triangles of the two
float polygons, mapped by the float `PolyZonotope.quadMapMixed` and enclosed by
`PolyZonotope.polygon`.
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

/-- The union of the polygons of the images of the pairs of triangles. -/
def Polygon.quadMapMixed (P₁ P₂ : Polygon 𝕋) (Q : Fin 2 → Mat 𝕋 2 2) (splits : ℕ)
    (pick : ℕ → PolyZonotope (Vec 𝕋 2) → Bool) : Polygon 𝕋 :=
  -- `list1 = triangulation(pgon1)` and `list2 = triangulation(pgon2)`
  let list₁ : List (VPolytope (Vec 𝕋 2)) := (Polygon.triangulation P₁).sets
  let list₂ : List (VPolytope (Vec 𝕋 2)) := (Polygon.triangulation P₂).sets
  -- per pair the mixed map of the two polynomial zonotopes, then its `polygon`
  ⟨list₁.flatMap fun t₁ => list₂.flatMap fun t₂ =>
    ((PolyZonotope.quadMapMixed Q t₁.polyZonotope t₂.polyZonotope).polygon splits pick).sets⟩

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
