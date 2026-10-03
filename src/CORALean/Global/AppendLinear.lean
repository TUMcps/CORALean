import CORALean.Global.Block
import Mathlib.LinearAlgebra.Pi

/-!
# A pair appended into one vector

`Fin.append` of a pair of real vectors as a linear map, the sum of the two block paddings: what a
Cartesian product of generator representations is read through.
-/

-- Authors:       Tobias Ladner
-- Written:       02-October-2026
-- Last update:   ---
-- Last revision: ---


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
