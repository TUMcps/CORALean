import CORALean.ContSet.Zonotope.Real.Zonotope
import CORALean.Global.Tensor
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# The generators up to and including `k` are those before `k` and `k`

`∑_{j < k+1} g_j = ∑_{j < k} g_j + g_k`: one step of the walk of [1, Alg. 3] adds one generator.

## References

* [1] A. Girard and C. Le Guernic. "Zonotope/Hyperplane Intersection for Hybrid Systems
      Reachability Analysis". In Hybrid Systems: Computation and Control (HSCC), LNCS 4981,
      Springer, 2008, pp. 215-228.
-/

-- Authors:       Tobias Ladner
-- Written:       11-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =======================================  MAIN THEOREM  ======================================= --

theorem Zonotope.sum_flip_succ (Z : Zonotope (Vec ℝ 2)) (k : Fin Z.h) :
    (∑ j, if decide (j.val < k.val + 1) = true then Z.G j else 0)
      = (∑ j, if decide (j.val < k.val) = true then Z.G j else 0) + Z.G k := by -- --- PROOF ---
  classical
  have : ∀ j : Fin Z.h, (if decide (j.val < k.val + 1) = true then Z.G j else 0)
      = (if decide (j.val < k.val) = true then Z.G j else 0) + (if j = k then Z.G j else 0) :=
    fun j => by
      by_cases h1 : j.val < k.val
      · have : j ≠ k := fun h => by rw [h] at h1; exact lt_irrefl _ h1
        simp [h1, this, Nat.lt_succ_of_lt h1]
      · by_cases h2 : j = k
        · subst h2; simp
        · have : ¬ j.val < k.val + 1 := fun h => h2 (Fin.ext (by omega))
          simp [h1, h2, this]
  simp only [this, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, if_true]

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
