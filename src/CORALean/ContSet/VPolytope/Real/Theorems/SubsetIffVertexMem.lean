module

public import CORALean.ContSet.VPolytope.Real.Theorems.ConvexHull

@[expose] public section

/-!
# V-polytope in V-polytope

[1, Eq. 3]: `⟨V₁⟩ ⊆ ⟨V₂⟩` exactly when every point of `V₁` lies in `⟨V₂⟩`, each tested by the
feasibility of [1, Eq. 4] — which is `VPolytope.construct` itself. The containing polytope is
convex, and that is all the argument uses.

## Inputs
* `P₁` – first polytope
* `P₂` – second polytope

## Hypotheses
* none

## Conclusion
* `P₁` lies in `P₂` iff every vertex of `P₁` does

## References

* [1] M. Wetzlinger, V. Kotsev, A. Kulmburg and M. Althoff. "Implementation of Polyhedral Operations
      in CORA 2024". Proceedings of the 11th Int. Workshop on Applied Verification for Continuous
      and Hybrid Systems, 2024.
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
