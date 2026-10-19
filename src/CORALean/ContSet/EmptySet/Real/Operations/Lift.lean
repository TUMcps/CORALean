module

public import CORALean.ContSet.EmptySet.Real.EmptySet

@[expose] public section

/-!
# `EmptySet.lift_`

CORA's `@emptySet/lift_`: only the dimension changes, to `N`. `dims` says which
coordinates of the high-dimensional space the old ones are.

## Inputs
* `_` – empty set
* `N` – target dimension
* `_` – coordinates of the old dimensions

## Output
* the empty set of dimension `N`
-/

-- Authors:       Claude Opus 5.5
-- Written:       01-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n m : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `emptySet/lift_`. -/
def EmptySet.lift_ (_ : EmptySet n) (N : ℕ) (_ : Fin n → Fin N) : EmptySet N := ⟨⟩

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
