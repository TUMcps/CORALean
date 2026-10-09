import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fintype.Basic
import CORALean.ContSet.Zonotope.Real.Operations.Tensor3

/-!
# `Zonotope.tensorEval`

The set `{ M_{ijk...l} x_j x_k ... x_l | x ∈ Z }` of CORA's `tensorMultiplication` at one point: for
a third-order tensor, component `iDim` is `Σ M{iDim}(a, b, c) xₐ x_b x_c`.
-/

-- Authors:       Tobias Ladner
-- Written:       08-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `Mᵢⱼₖₗ xⱼ xₖ xₗ` for one `x`. -/
def Zonotope.tensorEval (M : Zonotope.Tensor3 n) (x : Vec ℝ n) : Vec ℝ n :=
  fun iDim => ∑ a, ∑ b, ∑ c, M iDim a b c * x a * x b * x c

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
