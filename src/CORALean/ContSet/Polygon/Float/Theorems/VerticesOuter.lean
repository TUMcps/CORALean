module

public import CORALean.ContSet.Polygon.Float.Operations.Vertices
public import CORALean.ContSet.SetUnion.Theorems.Basic

@[expose] public section

/-!
# The polygon lies in the hull of its stored vertices, inflated by its error box

Each piece is its nominal polytope (the hull of the stored vertices,
`VPolytope.construct_eq_convexHull`) plus its error box, so a point of the polygon is a point of
the hull of all the stored vertices plus the error box of the piece it came from. Outer only: the
float polygon is the nominal one only up to those boxes.

## Inputs
* `P` – polygon

## Hypotheses
* none

## Conclusion
* the polygon lies in the hull of its stored vertices, inflated by its error box
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open Pointwise FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋]


-- =======================================  MAIN THEOREM  ======================================= --

theorem Polygon.vertices_outer (P : Polygon 𝕋) :
    ContSet.construct P ⊆ ⋃ p ∈ P.sets,
      (convexHull ℝ {v | v ∈ P.vertices.map toRealVec} + p.I_error.construct) := by -- --- PROOF ---
  intro x hx
  obtain ⟨p, hp, hxp⟩ := SetUnion.mem_construct.mp hx
  obtain ⟨y, hy, e, he, rfl⟩ := hxp
  refine Set.mem_biUnion hp ⟨y, ?_, e, he, rfl⟩
  have hy' : y ∈ convexHull ℝ (Set.range (Real.VPolytope.V (InflatedContSet.nominal p))) := by
    rw [← Real.VPolytope.construct_eq_convexHull]; exact hy
  refine convexHull_mono ?_ hy'
  rintro _ ⟨l, rfl⟩
  have hl : l.val < p.k := l.2
  refine List.mem_map.mpr ⟨p.V ⟨l.val, hl⟩, ?_, rfl⟩
  exact List.mem_flatMap.mpr ⟨p, hp, List.mem_ofFn.mpr ⟨⟨l.val, hl⟩, rfl⟩⟩

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
