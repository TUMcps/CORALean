module

public import CORALean.ContSet.Fullspace.Real.Fullspace

@[expose] public section

/-!
# `Fullspace.enclosePoints`

CORA's `@fullspace/enclosePoints`: `fullspace(size(points,1))`, the full space of the points'
dimension.

## Inputs
* `p` – number of points
* `_` – the points

## Output
* the full space of the points' dimension
-/

-- Authors:       Claude Opus 5.5
-- Written:       01-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n m : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `fullspace/enclosePoints`: the points are the columns of `points`. -/
def Fullspace.enclosePoints {p : ℕ} (_ : Fin p → Vec ℝ n) : Fullspace n := ⟨⟩

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
