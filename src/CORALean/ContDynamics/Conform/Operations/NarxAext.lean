import CORALean.Global.Tensor
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Logic.Equiv.Fin.Basic

/-!
# The extended output matrix of a NARX linearization

`A_ext,k` of [1, Cor. 2]: the state matrix of the window `(y_{k-n_p}, …, y_{k-1})`, identity
blocks one above the diagonal and the last block row `[A_{k,n_p} ⋯ A_{k,1}]`. The Jacobian
blocks `A_{k,i} = ∇_{y_{k-i}} h` arrive as a family `A` indexed by the lag `i`, so the block
in column `b` of the last row is `A (np - b)`; the window is `p` blocks of `ny`, block
`a` first, as `NonlinearARX.stack` reads it.

## References

* [1] L. Lützow and M. Althoff. "Reachset-Conformant System Identification". IEEE
      Transactions on Automatic Control, 71(5):3014-3029, 2026.
-/

-- Authors:       Tobias Ladner
-- Written:       11-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

variable {ny : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- [1, Cor. 2]: `A_ext,k` for the output Jacobians `A i = A_{k,i}`, `i = 1, …, np`. -/
def Conform.narxAext (np : ℕ) (A : ℕ → Mat ℝ ny ny) : Mat ℝ (np * ny) (np * ny) :=
  Matrix.of fun r c =>
    if (finProdFinEquiv.symm r).1.val + 1 < np then
      (if (finProdFinEquiv.symm c).1.val = (finProdFinEquiv.symm r).1.val + 1 ∧
          (finProdFinEquiv.symm c).2 = (finProdFinEquiv.symm r).2 then 1 else 0)
    else A (np - (finProdFinEquiv.symm c).1.val) (finProdFinEquiv.symm r).2
      (finProdFinEquiv.symm c).2

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
