module

public import CORALean.ContSet.Fullspace.Real.Fullspace

@[expose] public section

/-!
# `Fullspace.lift_`

CORA's `@fullspace/lift_`: only the dimension changes, to `N`; the new coordinates are
unbounded, as they are in the full space already.
-/

-- Authors:       Claude Opus 5.5
-- Written:       01-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n m : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `fullspace/lift_`. -/
def Fullspace.lift_ (_ : Fullspace n) (N : ℕ) (_ : Fin n → Fin N) : Fullspace N := ⟨⟩

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
