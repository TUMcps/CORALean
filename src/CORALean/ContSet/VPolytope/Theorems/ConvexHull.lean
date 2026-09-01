import CORALean.ContSet.VPolytope.Theorems.Convex

/-!
# A vertex description denotes the convex hull of its vertices

Both directions are the closure-operator property: the hull is the smallest
convex set containing the vertices, and the combinations are a convex set
containing them.

This is what makes the vertex operations cheap — `plus`, `map` and `linComb` are
then Mathlib's hull algebra applied to `Set.range V`, with no coefficient
bookkeeping of their own.
-/

-- Authors:       Tobias Ladner
-- Written:       01-September-2026
-- Last update:   ---
-- Last revision: ---

namespace CORALean.Real

variable {α : Type} [AddCommGroup α] [Module ℝ α]

theorem VPolytope.construct_eq_convexHull (P : VPolytope α) :
    P.construct = convexHull ℝ (Set.range P.V) := by
  apply Set.eq_of_subset_of_subset
  · rintro x ⟨β, hβ, hsum, rfl⟩
    exact Convex.sum_mem (convex_convexHull ℝ _) (fun j _ => hβ j) hsum
      fun j _ => subset_convexHull ℝ _ ⟨j, rfl⟩
  · exact convexHull_min (Set.range_subset_iff.mpr P.vertex_mem) P.convex_construct

end CORALean.Real
