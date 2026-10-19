module

public import CORALean.ContSet.EmptySet.Real.EmptySet

@[expose] public section

/-!
# `EmptySet.project`

CORA's `@emptySet/project`: only the dimension changes, to the number of kept coordinates.
`dims` lists the kept coordinates, as in CORA, and `Fin m → Fin n` is its range check.

## Inputs
* `_` – empty set
* `_` – coordinates kept

## Output
* the empty set in the kept dimension
-/

-- Authors:       Claude Opus 5.5
-- Written:       01-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n m : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `emptySet/project`. -/
def EmptySet.project (_ : EmptySet n) (_ : Fin m → Fin n) : EmptySet m := ⟨⟩

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
