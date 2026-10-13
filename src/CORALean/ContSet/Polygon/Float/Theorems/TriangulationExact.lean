import CORALean.ContSet.Polygon.Float.Operations.Triangulation
import CORALean.ContSet.Polygon.Real.Theorems.ConstructEqTriples
import CORALean.ContSet.VPolytope.Float.VPolytope

/-!
# `Polygon.triangulation` covers the float polygon's region

Exactly: every returned piece has three vertices, and the union of the triangles with their
boxes is what the float polygon denotes. A piece denotes its nominal hull plus the error box, the
real cover `VPolytope.construct_eq_iUnion_triples` splits the hull, and the box sum distributes
over the union. The statement is about the stored float polygon, not the real one.
-/

-- Authors:       Tobias Ladner
-- Written:       10-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --
namespace CORALean.Float

open FloatOps SoundFloatArithmetic InflatedContSet

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋]


-- =======================================  MAIN THEOREM  ======================================= --

theorem Polygon.triangulation_exact (P : Polygon 𝕋) :
    (∀ t ∈ (Polygon.triangulation P).sets, t.k = 3) ∧
      ContSet.construct (Polygon.triangulation P) = ContSet.construct P := by -- --- PROOF ---
  constructor
  · -- a returned set is a triple of vertices
    intro t ht
    simp only [Polygon.triangulation, List.mem_flatMap, List.mem_map] at ht
    obtain ⟨_, _, _, _, _, _, _, _, rfl⟩ := ht
    rfl
  · -- the nominal part of a triangle is the real triangle of the nominal vertices
    have hnom : ∀ (p : VPolytope (Vec 𝕋 2)) (a b c : Fin p.k),
        (nominal (⟨3, ![p.V a, p.V b, p.V c], p.E⟩ : VPolytope (Vec 𝕋 2))) =
          (⟨3, ![(nominal p).V a, (nominal p).V b, (nominal p).V c]⟩ :
            Real.VPolytope (Vec ℝ 2)) := fun p a b c => by
      show Real.VPolytope.mk 3 _ = _
      congr 1
      funext l
      fin_cases l <;> rfl
    -- a point is in a triangle iff it is in the piece the triangle belongs to
    ext x
    simp only [SetUnion.mem_construct, Polygon.triangulation, List.mem_flatMap, List.mem_map,
      List.mem_finRange, true_and]
    constructor
    · -- a point of a triangle is a point of its piece
      rintro ⟨_, ⟨p, hp, a, b, c, rfl⟩, y, hy, e, he, rfl⟩
      refine ⟨p, hp, y, ?_, e, he, rfl⟩
      change y ∈ Real.VPolytope.construct (nominal _) at hy
      rw [hnom] at hy
      change y ∈ Real.VPolytope.construct (nominal p)
      rw [Real.VPolytope.construct_eq_iUnion_triples]
      simp only [Set.mem_iUnion]
      exact ⟨a, b, c, hy⟩
    · -- a point of a piece is in one of its triangles, by Carathéodory
      rintro ⟨p, hp, y, hy, e, he, rfl⟩
      change y ∈ Real.VPolytope.construct (nominal p) at hy
      rw [Real.VPolytope.construct_eq_iUnion_triples] at hy
      simp only [Set.mem_iUnion] at hy
      obtain ⟨a, b, c, hy⟩ := hy
      refine ⟨_, ⟨p, hp, a, b, c, rfl⟩, y, ?_, e, he, rfl⟩
      change y ∈ Real.VPolytope.construct (nominal _)
      rw [hnom]
      exact hy

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
