module

public import CORALean.ContSet.VPolytope.Real.Theorems.ConvHullExact
public import CORALean.ContSet.VPolytope.Real.Theorems.Convex
public import CORALean.ContSet.ContSet.Theorems.ConvexHullUnionEqSegments

@[expose] public section

/-!
# The convex hull of two V-polytopes, by their points

[1, Eq. 30]: `conv(⟨V₁⟩, ⟨V₂⟩) = ⟨[V₁ V₂]⟩`, the paper's `conv` being
`{λ s₁ + (1 - λ) s₂}` [1, Table 3] — `segments`. That needs both polytopes nonempty: with
`⟨V₁⟩ = ∅` the left side is empty and the right side is `⟨V₂⟩`
(`segments_convHull_counterexample`). `VPolytope.convHull_exact` is the hull of the union,
which is what concatenating the lists gives at any operands.

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

theorem VPolytope.segments_eq_convHull (P₁ P₂ : VPolytope α) (h₁ : P₁.construct.Nonempty)
    (h₂ : P₂.construct.Nonempty) :
    segments P₁.construct P₂.construct = (P₁.convHull P₂).construct := by
  rw [VPolytope.convHull_exact,
    convexHull_union_eq_segments h₁ h₂ P₁.convex_construct P₂.convex_construct]

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
