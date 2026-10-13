import CORALean.Global.Tensor
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Real.Basic
import Mathlib.Logic.Equiv.Fin.Basic

/-!
# A sum over a window reads block by block

The window `(y_{k-n_p}, …, y_{k-1})` of [1, Cor. 2] is `np` blocks of `ny` coordinates under
`finProdFinEquiv`, so a sum over its coordinates is a sum over the blocks of a sum over each.

## References

* [1] L. Lützow and M. Althoff. "Reachset-Conformant System Identification". IEEE
      Transactions on Automatic Control, 71(5):3014-3029, 2026.
-/

-- Authors:       Claude Opus 5.5
-- Written:       11-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

variable {np ny : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- A sum over `np * ny` coordinates, block by block. -/
theorem Conform.sum_window (g : Fin (np * ny) → ℝ) :
    ∑ c, g c = ∑ b : Fin np, ∑ j : Fin ny, g (finProdFinEquiv (b, j)) := by
  rw [← Fintype.sum_prod_type', ← finProdFinEquiv.sum_comp g]

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
