import CORALean.ContSet.VPolytope.Real.Theorems.ConvexHull

/-!
# V-polytope in V-polytope

[1, Eq. 3]: `⟨V₁⟩ ⊆ ⟨V₂⟩` exactly when every point of `V₁` lies in `⟨V₂⟩`, each tested by the
feasibility of [1, Eq. 4] — which is `VPolytope.construct` itself. The containing polytope is
convex, and that is all the argument uses.

## References

* [1] M. Wetzlinger, V. Kotsev, A. Kulmburg and M. Althoff. "Implementation of Polyhedral
      Operations in CORA 2024". In Proc. of the 11th International Workshop on Applied
      Verification for Continuous and Hybrid Systems (ARCH24), EPiC Series in Computing,
      vol. 103, pp. 163-181, 2024.
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α : Type} [AddCommGroup α] [Module ℝ α]


-- =======================================  MAIN THEOREM  ======================================= --

theorem VPolytope.construct_subset_iff (P₁ P₂ : VPolytope α) :
    P₁.construct ⊆ P₂.construct ↔ ∀ l, P₁.V l ∈ P₂.construct := by
  rw [P₁.construct_eq_convexHull, P₂.convex_construct.convexHull_subset_iff, Set.range_subset_iff]

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
