module

public import CORALean.ContSet.Polygon.Real.Operations.Vertices
public import CORALean.ContSet.SetUnion.Theorems.Basic
public import CORALean.ContSet.VPolytope.Real.Instances

@[expose] public section

/-!
# The vertices of a polygon hold its hull

Every vertex is in the polygon, and the polygon is in the hull of its vertices; hence the two
hulls agree.

## Inputs
* `P` – polygon

## Hypotheses
* none

## Conclusion
* the hull of the stored vertices equals the hull of the polygon
-/

-- Authors:       Claude Opus 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

theorem Polygon.aux_mem_vertices_iff (P : Polygon) (v : Vec ℝ 2) :
    v ∈ P.vertices ↔ ∃ p ∈ P.sets, ∃ j, p.V j = v := by
  simp [Polygon.vertices, List.mem_flatMap, List.mem_ofFn]

theorem Polygon.aux_vertex_mem_construct (P : Polygon) {v : Vec ℝ 2} (hv : v ∈ P.vertices) :
    v ∈ ContSet.construct P := by
  obtain ⟨p, hp, j, rfl⟩ := (Polygon.aux_mem_vertices_iff P v).mp hv
  exact SetUnion.mem_construct.mpr ⟨p, hp, VPolytope.vertex_mem p j⟩

theorem Polygon.aux_construct_subset_convexHull_vertices (P : Polygon) :
    ContSet.construct P ⊆ convexHull ℝ {v | v ∈ P.vertices} := by -- --- PROOF ---
  intro x hx
  obtain ⟨p, hp, hx⟩ := SetUnion.mem_construct.mp hx
  have hx' : x ∈ convexHull ℝ (Set.range p.V) := by
    rw [← VPolytope.construct_eq_convexHull]; exact hx
  refine convexHull_mono ?_ hx'
  rintro _ ⟨j, rfl⟩
  exact (Polygon.aux_mem_vertices_iff P _).mpr ⟨p, hp, j, rfl⟩


-- =======================================  MAIN THEOREM  ======================================= --

theorem Polygon.convexHull_vertices (P : Polygon) :
    convexHull ℝ {v | v ∈ P.vertices} = convexHull ℝ (ContSet.construct P) :=
  Set.Subset.antisymm
    (convexHull_mono fun _ hv => Polygon.aux_vertex_mem_construct P hv)
    (convexHull_min (Polygon.aux_construct_subset_convexHull_vertices P) (convex_convexHull ℝ _))

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
