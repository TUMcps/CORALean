import CORALean.ContSet.Fullspace.Real.Fullspace

/-!
# `Fullspace.lift_`

CORA's `@fullspace/lift_`: only the dimension changes, to `N`; the new coordinates are
unbounded, as they are in the full space already.
-/

-- Authors:       Tobias Ladner
-- Written:       01-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n m : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `fullspace/lift_`. -/
def Fullspace.lift_ (_ : Fullspace n) (N : ℕ) (_ : Fin n → Fin N) : Fullspace N := ⟨⟩

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
