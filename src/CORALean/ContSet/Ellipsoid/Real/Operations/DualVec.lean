import CORALean.Global.Tensor

/-!
# `dualVec`

A functional on `Vec ℝ n` is a dot product, and `dualVec` is the vector it is
one with.
-/

-- Authors:       Tobias Ladner
-- Written:       02-September-2026
-- Last update:   05-September-2026
-- Last revision: ---

namespace CORALean.Real

variable {n : ℕ}

/-- The direction a functional is: `c` acts as the dot product with this vector,
which is what lets the support value be written with `Gᵀ`. -/
noncomputable def dualVec (c : Vec ℝ n →ₗ[ℝ] ℝ) : Vec ℝ n :=
  fun i => c fun j => if i = j then 1 else 0

end CORALean.Real
