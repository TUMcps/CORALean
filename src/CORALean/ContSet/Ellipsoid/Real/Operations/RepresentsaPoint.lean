module

public import CORALean.ContSet.Ellipsoid.Real.Ellipsoid

@[expose] public section

/-!
# `Ellipsoid.representsa_point`

CORA's `@ellipsoid/representsa_` at type `point` with tolerance `0`: the shape matrix vanishes,
`Q = 0`.

## Inputs
* `E` – ellipsoid

## Output
* the shape matrix is zero
-/

-- Authors:       Claude Opus 5.5
-- Written:       02-October-2026
-- Last update:   15-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `ellipsoid/representsa_` at `point`. -/
def Ellipsoid.representsa_point (E : Ellipsoid n) : Prop := E.Q = 0

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
