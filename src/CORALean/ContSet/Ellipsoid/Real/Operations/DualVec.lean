import CORALean.Global.Tensor
import Mathlib.Algebra.Module.LinearMap.Defs
import Mathlib.Data.Real.Basic

/-!
# `dualVec`

A functional on `Vec ℝ n` is a dot product, and `dualVec` is the vector it is
one with.
-/

-- Authors:       Claude Opus 5
-- Written:       02-September-2026
-- Last update:   05-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The direction a functional is: `c` acts as the dot product with this vector,
which is what lets the support value be written with `Gᵀ`. -/
noncomputable def dualVec (c : Vec ℝ n →ₗ[ℝ] ℝ) : Vec ℝ n :=
  fun i => c fun j => if i = j then 1 else 0

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
