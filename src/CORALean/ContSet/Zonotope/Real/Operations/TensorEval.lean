module

public import CORALean.Global.Tensor
public import Mathlib.Data.Real.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Data.Fintype.Basic

@[expose] public section

/-!
# `Zonotope.tensorEval`

The set `{ M_{ijk...l} x_j x_k ... x_l | x ∈ Z }` of CORA's `tensorMultiplication` at one point: for
a third-order tensor, component `iDim` is `Σ M{iDim}(a, b, c) xₐ x_b x_c`.
-/

-- Authors:       Claude Opus 5.5
-- Written:       08-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `Mᵢⱼₖₗ xⱼ xₖ xₗ` for one `x`. -/
def Zonotope.tensorEval (M : Tensor3 ℝ n) (x : Vec ℝ n) : Vec ℝ n :=
  fun iDim => ∑ a, ∑ b, ∑ c, M iDim a b c * x a * x b * x c

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
