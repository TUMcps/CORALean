module

public import CORALean.Global.Tensor
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Data.Fintype.Fin
public import Mathlib.Data.Real.Basic

@[expose] public section

/-!
# The scaling of the Lipschitz-constrained linear layer

CORA's `computeWeightNorm`: `N = diag(1 ./ max(1, λ⁻¹ Σⱼ |Wᵢⱼ|))`, which divides each row by its
absolute row sum over `λ` whenever that exceeds `1`, so the rows of `N W` have absolute sum at
most `λ`.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

variable {n m : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The diagonal of `N`: `1 ./ max(1, λ⁻¹ Σⱼ |Wᵢⱼ|)`. -/
noncomputable def Layer.lipConstrScale (W : Mat ℝ m n) (lam : ℝ) : Vec ℝ m :=
  fun i => 1 / max 1 (lam⁻¹ * ∑ j, |W i j|)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
