import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fintype.Basic
import CORALean.Global.Tensor

/-!
# `Zonotope.Tensor3`

The third-order tensors of CORA's `@zonotope/tensorMultiplication.m`: `M = {M₁, ..., Mₙ}` with
`Mᵢ` an `n × n × n` array, `M{iDim}(ind1, ind2, ind3)`. A function type, so a real module, and a
matrix zonotope of tensors is a `Zonotope` over it.
-/

-- Authors:       Tobias Ladner
-- Written:       08-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- A third-order tensor, `M{iDim}(ind1, ind2, ind3)`, as `M iDim ind1 ind2 ind3`. -/
abbrev Zonotope.Tensor3 (n : ℕ) : Type := Fin n → Fin n → Fin n → Fin n → ℝ

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
