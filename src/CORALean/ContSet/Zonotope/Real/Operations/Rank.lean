module

public import CORALean.ContSet.Zonotope.Real.Zonotope
public import Mathlib.LinearAlgebra.Dimension.Finrank

@[expose] public section

/-!
# `Zonotope.rank`

CORA's `@zonotope/rank`: the rank of the generator matrix, here the dimension of the span of the
generators. Exact, where CORA's `rank(Z.G, tol)` drops singular values below a tolerance (default
`0`).
-/

-- Authors:       Claude Opus 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α : Type} [AddCommGroup α] [Module ℝ α]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `zonotope/rank`. -/
noncomputable def Zonotope.rank (Z : Zonotope α) : ℕ :=
  Module.finrank ℝ (Submodule.span ℝ (Set.range Z.G))

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
