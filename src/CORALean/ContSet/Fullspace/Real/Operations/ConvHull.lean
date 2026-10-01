import CORALean.ContSet.Fullspace.Real.Fullspace
import CORALean.ContSet.ContSet.ContSet

/-!
# `Fullspace.convHull`

CORA's `@fullspace/convHull_`: the hull of the full space and anything is the full space.
-/

-- Authors:       Tobias Ladner
-- Written:       01-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `fullspace/convHull_`: the full space. -/
def Fullspace.convHull (F : Fullspace n) {S : Type} (_ : S) : Fullspace n := F

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
