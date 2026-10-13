import CORALean.Global.Tensor
import Mathlib.Data.Real.Basic

/-!
# The sub-boxes of the normalized box

Boxes whose four ends lie in `[-1, 1]`, the boxes [1, Sec. 4]'s optimizer works on for a model
over the normalized box; halving keeps them so.

## References

* [1] K. Makino and M. Berz. "Verified Global Optimization with Taylor Model-based Range
      Bounders". Transactions on Computers, 11(4):1611-1618, 2005.
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def Taylm.GoodBox (B : Fin n → ℝ × ℝ) : Prop :=
  ∀ k, -1 ≤ (B k).1 ∧ (B k).1 ≤ 1 ∧ -1 ≤ (B k).2 ∧ (B k).2 ≤ 1

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
