module

public import CORALean.Global.Block
public import Mathlib.LinearAlgebra.Pi

@[expose] public section

/-!
# A pair appended into one vector

`Fin.append` of a pair of real vectors as a linear map, the sum of the two block paddings: what a
Cartesian product of generator representations is read through.

## Inputs
* `n₁` – dimension of the first vector
* `n₂` – dimension of the second vector

## Output
* the linear map appending a pair into one vector
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean


variable {n₁ n₂ : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def appendLinear (n₁ n₂ : ℕ) : (Vec ℝ n₁ × Vec ℝ n₂) →ₗ[ℝ] Vec ℝ (n₁ + n₂) :=
  (blockPadLeft n₁ n₂).coprod (blockPadRight n₁ n₂)

theorem appendLinear_apply (p : Vec ℝ n₁ × Vec ℝ n₂) :
    appendLinear n₁ n₂ p = Fin.append p.1 p.2 := by
  funext j
  refine Fin.addCases (fun i => ?_) (fun i => ?_) j <;>
    simp [appendLinear, blockPadLeft, blockPadRight]

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
