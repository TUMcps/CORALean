module

public import CORALean.ContSet.EmptySet.Real.EmptySet

@[expose] public section

/-!
# `EmptySet.vertices`

CORA's `@emptySet/vertices_`: `zeros(dim(O),0)`, an `n × 0` matrix, which is a family of
no vertices in `Vec ℝ n`.

## Inputs
* `_` – empty set

## Output
* the empty family of vertices
-/

-- Authors:       Claude Opus 5.5
-- Written:       01-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n m : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `emptySet/vertices_`: no vertices. -/
def EmptySet.vertices (_ : EmptySet n) : Fin 0 → Vec ℝ n := Fin.elim0

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
