import CORALean.Global.Tensor
import Mathlib.Data.Real.Basic
import Mathlib.Data.Matrix.Mul

/-!
# The outer square of an image

`(M x)(M x)ᵀ = M (x xᵀ) Mᵀ`: a generator mapped by `M` contributes `M (g gᵀ) Mᵀ` to the
generator Gram matrix `H Hᵀ`, which is how `P₊ = Ĥ₊ Ĥ₊ᵀ` of the zonotopic observers is
assembled from its blocks.
-/

-- Authors:       Tobias Ladner
-- Written:       04-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix

variable {n m : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem vecMulVec_mulVec_self (M : Mat ℝ n m) (x : Vec ℝ m) :
    vecMulVec (M *ᵥ x) (M *ᵥ x) = M * vecMulVec x x * Mᵀ := by
  ext a b
  simp only [vecMulVec_apply, mulVec, dotProduct, mul_apply, transpose_apply, Finset.sum_mul,
    Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
