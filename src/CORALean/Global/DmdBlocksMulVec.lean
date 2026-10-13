import CORALean.Global.DmdBlocks
import Mathlib.Data.Matrix.Mul
import Mathlib.Algebra.BigOperators.Fin

/-!
# The blocks act on the regressor as the matrix does

`[A c B] [x; 1; u] = A x + B u + c`: what makes a fit of the stacked matrix a fit of the
three.
The source is [1].

## References

* [1] `contDynamics/@linearSysDT/private/priv_identifyDMD.m`
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix

variable {n m : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem dmdBlocks_mulVec (M : Mat ℝ n (n + 1 + m)) (x : Vec ℝ n) (u : Vec ℝ m) :
    M *ᵥ dmdRegressor x u
      = (dmdBlocks M).1 *ᵥ x + (dmdBlocks M).2.1 *ᵥ u + (dmdBlocks M).2.2 := by -- --- PROOF ---
  funext i
  -- the sum over `Fin (n + 1 + m)` splits into the state, the `1` and the input
  simp only [Matrix.mulVec, dotProduct, Pi.add_apply, dmdBlocks, dmdRegressor]
  rw [Fin.sum_univ_add, Fin.sum_univ_castSucc]
  simp [Fin.append_left, Fin.append_right, Fin.snoc_castSucc, Fin.snoc_last]
  ring

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
