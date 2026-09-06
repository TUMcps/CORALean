import CORALean.ContSet.VPolytope.Real.Operations.Plus
import CORALean.ContSet.VPolytope.Real.Theorems.ConvexHull

/-!
# `VPolytope.plus` is exactly the Minkowski sum

All of the content is `convexHull_add`: the hull of a sum is the sum of the
hulls. What is left is that the pairwise vertex sums range over exactly the sum
of the two vertex sets, which `finProdFinEquiv` makes a bijection rather than a
counting argument.
-/

-- Authors:       Tobias Ladner
-- Written:       01-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Pointwise

variable {α : Type} [AddCommGroup α] [Module ℝ α]


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

omit [Module ℝ α] in
theorem VPolytope.aux_range_plus (P₁ P₂ : VPolytope α) :
    Set.range (P₁.plus P₂).V = Set.range P₁.V + Set.range P₂.V := by
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
