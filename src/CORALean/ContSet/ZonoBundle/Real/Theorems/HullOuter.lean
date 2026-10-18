module

public import CORALean.ContSet.SetIntersection.Theorems.Basic
public import CORALean.ContSet.ZonoBundle.Real.ZonoBundle
public import Mathlib.Analysis.Convex.Hull

@[expose] public section

/-!
# The hull of a bundle and its image, member by member

[1, Prop. 5]: `CH(Z_∩ ∪ L Z_∩) ⊆ {CH(Z₁ ∪ L Z₁), …, CH(Z_s ∪ L Z_s)}_∩`, for any
linear `L`. Convex hull is monotone and `Z_∩ ⊆ Zᵢ`; the printed proof goes through
scalings and Minkowski sums, which this does not need.

## References

* [1] M. Althoff and B. H. Krogh. "Zonotope Bundles for the Efficient Computation of
      Reachable Sets". In Proc. of the 50th IEEE Conference on Decision and Control and
      European Control Conference (CDC-ECC), pp. 6814-6821, 2011.
-/

-- Authors:       Claude Opus 5.5
-- Written:       01-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α : Type} [AddCommGroup α] [Module ℝ α]


-- =======================================  MAIN THEOREM  ======================================= --

theorem ZonoBundle.hull_outer (zB : ZonoBundle α) (L : α →ₗ[ℝ] α) :
    convexHull ℝ (zB.construct ∪ L '' zB.construct) ⊆
      ⋂ i, convexHull ℝ ((zB.Z i).construct ∪ L '' (zB.Z i).construct) := by
  refine Set.subset_iInter fun i => convexHull_mono ?_
  have h : zB.construct ⊆ (zB.Z i).construct := SetIntersection.construct_subset_ofFn _ i
  exact Set.union_subset_union h (Set.image_mono h)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
