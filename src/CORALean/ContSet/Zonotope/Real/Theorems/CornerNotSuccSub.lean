module

public import CORALean.ContSet.Zonotope.Real.Theorems.CornerEqBottomAdd
public import CORALean.ContSet.Zonotope.Real.Theorems.SumFlipSucc
public import CORALean.ContSet.Zonotope.Real.Theorems.SumFlipCompl
public import Mathlib.Tactic.Module

@[expose] public section

/-!
# The second block of the walk subtracts `2 g_k` at step `k`

`corner (¬ j < k + 1) = corner (¬ j < k) - 2 g_k`: the second loop of [1, Alg. 3] moves from
`P` to `P - 2g`.

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

theorem Zonotope.corner_not_succ_sub (Z : Zonotope (Vec ℝ 2)) (k : Fin Z.h) :
    Z.corner (fun j => !decide (j.val < k.val + 1))
      = Z.corner (fun j => !decide (j.val < k.val)) + -((2 : ℝ) • Z.G k) := by -- --- PROOF ---
  have hc := Zonotope.sum_flip_compl Z (fun j => decide (j.val < k.val))
  have hc' := Zonotope.sum_flip_compl Z (fun j => decide (j.val < k.val + 1))
  have hs := Zonotope.sum_flip_succ Z k
  rw [Zonotope.corner_eq_bottom_add, Zonotope.corner_eq_bottom_add]
  have : (∑ j, if (!decide (j.val < k.val + 1)) = true then Z.G j else 0)
      = (∑ j, if (!decide (j.val < k.val)) = true then Z.G j else 0) - Z.G k := by
    rw [hs] at hc'
    linear_combination hc' - hc
  rw [this]
  module

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
