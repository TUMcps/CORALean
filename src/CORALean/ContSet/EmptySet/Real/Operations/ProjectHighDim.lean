import CORALean.ContSet.EmptySet.Real.EmptySet

/-!
# `EmptySet.projectHighDim_`

CORA's `@emptySet/projectHighDim_`: only the dimension changes, to `N`; the new
coordinates are the ones held at zero.
-/

-- Authors:       Claude Opus 5.5
-- Written:       01-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n m : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `emptySet/projectHighDim_`. -/
def EmptySet.projectHighDim_ (_ : EmptySet n) (N : ℕ) (_ : Fin n → Fin N) : EmptySet N := ⟨⟩

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
