import CORALean.ContSet.VPolytope.Real.Operations.ConvHull
import CORALean.ContSet.VPolytope.Real.Theorems.ConvexHull

/-!
# `VPolytope.convHull` is exactly the convex hull of the union

An equality: the hull of the concatenated vertices is the hull of the vertex sets together, which
is the hull of the two polytopes, a polytope being the hull of its vertices.
-/

-- Authors:       Claude Opus 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =======================================  MAIN THEOREM  ======================================= --

theorem VPolytope.convHull_exact {α : Type} [AddCommGroup α] [Module ℝ α] (P Q : VPolytope α) :
    (P.convHull Q).construct = convexHull ℝ (P.construct ∪ Q.construct) := by -- --- PROOF ---
  rw [VPolytope.construct_eq_convexHull, VPolytope.construct_eq_convexHull,
    VPolytope.construct_eq_convexHull, convexHull_convexHull_union_left,
    convexHull_convexHull_union_right]
  congr 1
  ext v
  simp only [VPolytope.convHull, Set.mem_range, Set.mem_union]
  constructor
  · rintro ⟨i, rfl⟩
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · exact Or.inl ⟨j, by simp⟩
    · exact Or.inr ⟨j, by simp⟩
  · rintro (⟨j, rfl⟩ | ⟨j, rfl⟩)
    · exact ⟨Fin.castAdd _ j, by simp⟩
    · exact ⟨Fin.natAdd _ j, by simp⟩

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
