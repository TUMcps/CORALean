import CORALean.ContSet.Polygon.Real.Operations.Triangulation
import CORALean.ContSet.Polygon.Real.Theorems.ConstructEqTriples

/-!
# `Polygon.triangulation` is a cover by triangles of the same region

Exactly: every returned set has three vertices and their union is the region of the polygon
(`VPolytope.construct_eq_iUnion_triples` for each piece). The triangles need not be disjoint.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       10-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --
namespace CORALean.Real


-- =======================================  MAIN THEOREM  ======================================= --

theorem Polygon.triangulation_exact (P : Polygon) :
    (∀ t ∈ (Polygon.triangulation P).sets, t.k = 3) ∧
      ContSet.construct (Polygon.triangulation P) = ContSet.construct P := by -- --- PROOF ---
  constructor
  · -- a returned set is a triple of vertices
    intro t ht
    simp only [Polygon.triangulation, List.mem_flatMap, List.mem_map] at ht
    obtain ⟨_, _, _, _, _, _, _, _, rfl⟩ := ht
    rfl
  · -- a point is in a triangle iff it is in the piece the triangle belongs to
    ext x
    simp only [SetUnion.mem_construct, Polygon.triangulation, List.mem_flatMap, List.mem_map,
      List.mem_finRange, true_and]
    constructor
    · -- a point of a triangle is a point of its piece
      rintro ⟨_, ⟨p, hp, a, b, c, rfl⟩, hx⟩
      refine ⟨p, hp, ?_⟩
      show x ∈ VPolytope.construct p
      rw [VPolytope.construct_eq_iUnion_triples]
      simp only [Set.mem_iUnion]
      exact ⟨a, b, c, hx⟩
    · -- a point of a piece is in one of its triangles, by Carathéodory
      rintro ⟨p, hp, hx⟩
      change x ∈ VPolytope.construct p at hx
      rw [VPolytope.construct_eq_iUnion_triples] at hx
      simp only [Set.mem_iUnion] at hx
      obtain ⟨a, b, c, hx⟩ := hx
      exact ⟨_, ⟨p, hp, a, b, c, rfl⟩, hx⟩

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
