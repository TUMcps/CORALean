import CORALean.ContSet.Zonotope.Real.Zonotope
import CORALean.Global.Tensor
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# The generators selected and those not selected make up all of them

`∑_{¬ s j} g_j + ∑_{s j} g_j = ∑ g_j`: the two blocks of the walk of [1, Alg. 3] are complementary.

## References

* [1] A. Girard and C. Le Guernic. "Zonotope/Hyperplane Intersection for Hybrid Systems
      Reachability Analysis". In Hybrid Systems: Computation and Control (HSCC), LNCS 4981,
      Springer, 2008, pp. 215-228.
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
