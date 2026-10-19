module

public import CORALean.ContSet.Fullspace.Real.Fullspace

@[expose] public section

/-!
# `Fullspace.project`

CORA's `@fullspace/project`: only the dimension changes, to the number of kept
coordinates. CORA throws at `n = 0`; nothing here does.

## Inputs
* `_` – full space
* `_` – coordinates kept

## Output
* the full space in the kept dimension
-/

-- Authors:       Claude Opus 5.5
-- Written:       01-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n m : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `fullspace/project`. -/
def Fullspace.project (_ : Fullspace n) (_ : Fin m → Fin n) : Fullspace m := ⟨⟩

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
