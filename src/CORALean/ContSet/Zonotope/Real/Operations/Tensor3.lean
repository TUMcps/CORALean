module

public import Mathlib.Data.Real.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Data.Fintype.Basic
public import CORALean.Global.Tensor

@[expose] public section

/-!
# `Zonotope.Tensor3`

The third-order tensors of CORA's `@zonotope/tensorMultiplication.m`: `M = {M₁, ..., Mₙ}` with
`Mᵢ` an `n × n × n` array, `M{iDim}(ind1, ind2, ind3)`. A function type, so a real module, and a
matrix zonotope of tensors is a `Zonotope` over it.
-/

-- Authors:       Claude Opus 5.5
-- Written:       08-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- A third-order tensor, `M{iDim}(ind1, ind2, ind3)`, as `M iDim ind1 ind2 ind3`. -/
abbrev Zonotope.Tensor3 (n : ℕ) : Type := Fin n → Fin n → Fin n → Fin n → ℝ

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
