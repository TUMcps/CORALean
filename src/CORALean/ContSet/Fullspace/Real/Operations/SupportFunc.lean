import CORALean.ContSet.Fullspace.Real.Fullspace
import Mathlib.Data.EReal.Basic

/-!
# `Fullspace.supportFunc`

CORA's `@fullspace/supportFunc_` for type `'upper'`: `Inf`, the supremum of a nonzero linear
functional over the whole space. At the zero direction the supremum is `0`. A value of `EReal`,
as `EmptySet.supportFunc`.
-/

-- Authors:       Tobias Ladner
-- Written:       01-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

open Classical in
/-- `fullspace/supportFunc_`, `'upper'`: `Inf` for a nonzero direction, `0` for the zero one. -/
noncomputable def Fullspace.supportFunc (_ : Fullspace n) (c : Vec ℝ n →ₗ[ℝ] ℝ) : EReal :=
  if c = 0 then 0 else ⊤

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
