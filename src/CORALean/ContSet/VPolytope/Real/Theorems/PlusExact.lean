module

public import CORALean.ContSet.VPolytope.Real.Operations.Plus
public import CORALean.ContSet.VPolytope.Real.Theorems.ConvexHull

@[expose] public section

/-!
# `VPolytope.plus` is exactly the Minkowski sum

All of the content is `convexHull_add`: the hull of a sum is the sum of the
hulls. What is left is that the pairwise vertex sums range over exactly the sum
of the two vertex sets, which `finProdFinEquiv` makes a bijection rather than a
counting argument.

This is [1, Eq. 25], the Minkowski sum of two V-polytopes as all pairwise sums of their points.

## Inputs
* `P₁` – first polytope
* `P₂` – second polytope

## Hypotheses
* none

## Conclusion
* the Minkowski sum is exactly the result

## References

* [1] M. Wetzlinger, V. Kotsev, A. Kulmburg and M. Althoff. "Implementation of Polyhedral
      Operations in CORA 2024". In Proc. of the 11th International Workshop on Applied
      Verification for Continuous and Hybrid Systems (ARCH24), EPiC Series in Computing,
      vol. 103, pp. 163-181, 2024.
-/

-- Authors:       Claude Opus 5
-- Written:       01-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Pointwise

variable {α : Type} [AddCommGroup α] [Module ℝ α]


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

omit [Module ℝ α] in
theorem VPolytope.aux_range_plus (P₁ P₂ : VPolytope α) : -- --- CONCL ---
    Set.range (P₁.plus P₂).V = Set.range P₁.V + Set.range P₂.V := by -- --- PROOF ---
  apply Set.eq_of_subset_of_subset
  · rintro _ ⟨l, rfl⟩
    exact ⟨P₁.V _, ⟨_, rfl⟩, P₂.V _, ⟨_, rfl⟩, rfl⟩
  · rintro _ ⟨_, ⟨j₁, rfl⟩, _, ⟨j₂, rfl⟩, rfl⟩
    refine ⟨finProdFinEquiv (j₁, j₂), ?_⟩
    show P₁.V (finProdFinEquiv.symm (finProdFinEquiv (j₁, j₂))).1
      + P₂.V (finProdFinEquiv.symm (finProdFinEquiv (j₁, j₂))).2 = _
    rw [Equiv.symm_apply_apply]


-- =======================================  MAIN THEOREM  ======================================= --

theorem VPolytope.plus_exact (P₁ P₂ : VPolytope α) :
    P₁.construct + P₂.construct = (P₁.plus P₂).construct := by
  rw [VPolytope.construct_eq_convexHull P₁, VPolytope.construct_eq_convexHull P₂,
    VPolytope.construct_eq_convexHull (P₁.plus P₂), VPolytope.aux_range_plus, convexHull_add]

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
