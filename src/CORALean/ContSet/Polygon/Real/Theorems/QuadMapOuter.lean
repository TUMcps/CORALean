module

public import CORALean.ContSet.Polygon.Real.Operations.QuadMap
public import CORALean.ContSet.Polygon.Real.Theorems.TriangulationExact
public import CORALean.ContSet.PolyZonotope.Real.Theorems.QuadMapExact
public import CORALean.ContSet.PolyZonotope.Real.Theorems.PolygonOuter
public import CORALean.ContSet.Conversion.Real.Operations.Basic
public import CORALean.ContSet.Conversion.Real.Operations.Zonotope_to_PolyZonotope
public import CORALean.ContSet.Conversion.Real.Theorems.Basic

@[expose] public section

/-!
# `Polygon.quadMap` encloses the image of the region

Outer: a point of the region lies in a triangle of the cover, which the box conversion places
in its polynomial zonotope; `quadMap_exact` maps it into the image polynomial zonotope and
`polygon_outer` into its polygon. Nothing is said of how much larger than the image the result
is. CORA states the result as a tight enclosure and computes the boundary of the images
(`polygon(pZ)`), which `polygon_outer` is the enclosure counterpart of.

## Inputs
* `P` – polygon
* `Q` – matrices indexed by `Fin 2`
* `splits` – number of splits
* `pick` – refinement rule: whether to split a piece in a given round

## Hypotheses
* none

## Conclusion
* `Polygon.quadMap` encloses the image of the region
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       10-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --
namespace CORALean.Real


-- =======================================  MAIN THEOREM  ======================================= --

theorem Polygon.quadMap_outer (P : Polygon) (Q : Fin 2 → Mat ℝ 2 2) (splits : ℕ)
    (pick : ℕ → PolyZonotope (Vec ℝ 2) → Bool) : -- --- CONCL ---
    PolyZonotope.quadEval Q '' ContSet.construct P
      ⊆ ContSet.construct (P.quadMap Q splits pick) := by -- --- PROOF ---
  rintro _ ⟨x, hx, rfl⟩
  -- the point lies in a triangle of the cover
  rw [← (Polygon.triangulation_exact P).2] at hx
  obtain ⟨t, ht, hxt⟩ := SetUnion.mem_construct.mp hx
  -- its image lies in the polygon of the image of the triangle's polynomial zonotope
  have himg : PolyZonotope.quadEval Q x ∈ (t.polyZonotope.quadMap Q).construct :=
    (PolyZonotope.quadMap_exact Q t.polyZonotope).subset
      ⟨x, VPolytope.polyZonotope_contains t hxt, rfl⟩
  have hpoly := PolyZonotope.polygon_outer (t.polyZonotope.quadMap Q) splits pick himg
  obtain ⟨s, hs, hxs⟩ := SetUnion.mem_construct.mp hpoly
  exact SetUnion.mem_construct.mpr ⟨s, List.mem_flatMap.mpr ⟨t, ht, hs⟩, hxs⟩

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
