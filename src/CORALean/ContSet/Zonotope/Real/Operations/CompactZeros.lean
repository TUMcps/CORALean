import CORALean.ContSet.Zonotope.Real.Operations.FilterGen

/-!
# `Zonotope.compactZeros`

CORA's `@zonotope/compact_.m` with method `'zeros'`: `Z.G = nonzeroFilter(Z.G, tol)`, the
generators that are not zero (every entry within `tol` of zero) are dropped. Here the tolerance
is `0`, the only one at which the operation is exact: with `tol > 0` CORA drops short non-zero
generators, which shrinks the set. The method `'all'` (merging parallel generators) is not
covered.
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open scoped Classical

variable {α : Type} [AddCommGroup α] [Module ℝ α]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- Drop the generators that are exactly zero. -/
noncomputable def Zonotope.compactZeros (Z : Zonotope α) : Zonotope α :=
  Z.filterGen fun j => decide (Z.G j ≠ 0)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
