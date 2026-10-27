module

public import CORALean.ContSet.VPolytope.Real.Theorems.ConvHullExact
public import CORALean.ContSet.VPolytope.Real.Theorems.Convex
public import CORALean.ContSet.ContSet.Theorems.ConvexHullUnionEqSetLinComb

@[expose] public section

/-!
# The convex hull of two V-polytopes, by their points

[1, Eq. 30]: `conv(⟨V₁⟩, ⟨V₂⟩) = ⟨[V₁ V₂]⟩`, the paper's `conv` being
`{λ s₁ + (1 - λ) s₂}` [1, Table 3] — `Set.linComb`. That needs both polytopes nonempty: with
`⟨V₁⟩ = ∅` the left side is empty and the right side is `⟨V₂⟩`
(`setLinComb_convHull_counterexample`). `VPolytope.convHull_exact` is the hull of the union,
which is what concatenating the lists gives at any operands.

## Inputs
* `P₁` – first polytope
* `P₂` – second polytope

## Hypotheses
* `h₁` – `P₁` nonempty
* `h₂` – `P₂` nonempty

## Conclusion
* the linear combination is exactly the convex hull

## References

* [1] [M. Wetzlinger, V. Kotsev, A. Kulmburg and M. Althoff. "Implementation of Polyhedral
      Operations in CORA 2024". Proceedings of the 11th Int. Workshop on Applied Verification for
      Continuous and Hybrid Systems,
      2024.](../../../../../../references/2024/wetzlinger-arch-polyhedral-operations.md)
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α : Type} [AddCommGroup α] [Module ℝ α]


-- =======================================  MAIN THEOREM  ======================================= --

theorem VPolytope.setLinComb_eq_convHull (P₁ P₂ : VPolytope α) (h₁ : P₁.construct.Nonempty)
    (h₂ : P₂.construct.Nonempty) :
    Set.linComb P₁.construct P₂.construct = (P₁.convHull P₂).construct := by
  rw [VPolytope.convHull_exact,
    convexHull_union_eq_setLinComb h₁ h₂ P₁.convex_construct P₂.convex_construct]

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
