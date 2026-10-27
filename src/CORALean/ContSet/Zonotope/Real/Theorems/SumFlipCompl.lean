module

public import CORALean.ContSet.Zonotope.Real.Zonotope
public import CORALean.Global.Tensor
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic

@[expose] public section

/-!
# The generators selected and those not selected make up all of them

`∑_{¬ s j} g_j + ∑_{s j} g_j = ∑ g_j`: the two blocks of the walk of [1, Alg. 3] are complementary.

## Inputs
* `Z` – planar zonotope
* `s` – corner signs

## Hypotheses
* none

## Conclusion
* complementary signs sum to all generators

## References

* [1] [A. Girard and C. Le Guernic. "Zonotope/Hyperplane Intersection for Hybrid Systems
      Reachability Analysis". Hybrid Systems: Computation and Control,
      2008.](../../../../../../references/2008/girard-hscc-zonotope-hyperplane.md)
-/

-- Authors:       Claude Opus 5.5
-- Written:       11-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =======================================  MAIN THEOREM  ======================================= --

theorem Zonotope.sum_flip_compl (Z : Zonotope (Vec ℝ 2)) (s : Fin Z.h → Bool) :
    (∑ j, if (!s j) = true then Z.G j else 0) + (∑ j, if s j = true then Z.G j else 0)
      = ∑ j, Z.G j := by
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun j _ => by cases s j <;> simp

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
