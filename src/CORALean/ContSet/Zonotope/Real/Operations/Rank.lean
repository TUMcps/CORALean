import CORALean.ContSet.Zonotope.Real.Zonotope
import Mathlib.LinearAlgebra.Dimension.Finrank

/-!
# `Zonotope.rank`

CORA's `@zonotope/rank`: the rank of the generator matrix, here the dimension of the span of the
generators. Exact, where CORA's `rank(Z.G, tol)` drops singular values below a tolerance (default
`0`).
-/

-- Authors:       Tobias Ladner
-- Written:       02-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α : Type} [AddCommGroup α] [Module ℝ α]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `zonotope/rank`. -/
noncomputable def Zonotope.rank (Z : Zonotope α) : ℕ :=
  Module.finrank ℝ (Submodule.span ℝ (Set.range Z.G))

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
