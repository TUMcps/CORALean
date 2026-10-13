module

public import CORALean.ContSet.Polygon.Float.Operations.QuadMap
public import CORALean.ContSet.Polygon.Float.Theorems.TriangulationExact
public import CORALean.ContSet.PolyZonotope.Float.Theorems.QuadMapOuter
public import CORALean.ContSet.PolyZonotope.Float.Theorems.PolygonOuter

@[expose] public section

/-!
# `Polygon.quadMap` encloses the image of the float polygon

Outer: the same chain as over ℝ, with the float triangulation (exact), the box conversion
(`VPolytope.polyZonotope_contains`), `PolyZonotope.quadMap_outer` and
`PolyZonotope.polygon_outer`. The quadratic map is that of the matrices the floats read as.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       10-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --
namespace CORALean.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋]


-- =======================================  MAIN THEOREM  ======================================= --

theorem Polygon.quadMap_outer (P : Polygon 𝕋) (Q : Fin 2 → Mat 𝕋 2 2) (splits : ℕ)
    (pick : ℕ → PolyZonotope (Vec 𝕋 2) → Bool) :
    Real.PolyZonotope.quadEval (fun k => toRealMat (Q k)) '' ContSet.construct P
      ⊆ ContSet.construct (P.quadMap Q splits pick) := by -- --- PROOF ---
  rintro _ ⟨x, hx, rfl⟩
  -- the point lies in a triangle of the cover
  rw [← (Polygon.triangulation_exact P).2] at hx
  obtain ⟨t, ht, hxt⟩ := SetUnion.mem_construct.mp hx
  -- its image lies in the polygon of the image of the triangle's polynomial zonotope
  have himg := PolyZonotope.quadMap_outer Q t.polyZonotope
    ⟨x, VPolytope.polyZonotope_contains t hxt, rfl⟩
  have hpoly := PolyZonotope.polygon_outer (PolyZonotope.quadMap Q t.polyZonotope) splits pick himg
  obtain ⟨s, hs, hxs⟩ := SetUnion.mem_construct.mp hpoly
  exact SetUnion.mem_construct.mpr ⟨s, List.mem_flatMap.mpr ⟨t, ht, hs⟩, hxs⟩

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
