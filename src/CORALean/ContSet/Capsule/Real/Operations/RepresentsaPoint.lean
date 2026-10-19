module

public import CORALean.ContSet.Capsule.Real.Capsule

@[expose] public section

/-!
# `Capsule.representsa_point`

CORA's `@capsule/representsa_.m` at `point`: `isPoint = all(withinTol(C.g, 0, tol)) &&
withinTol(C.r, 0, tol)`, here at tolerance `0`. The `emptySet` type of the same file is
`isempty(C.c) || isempty(C.g) || isempty(C.r)`, which a capsule of this model never is.

## Inputs
* `C` – capsule

## Output
* `Prop` that `C` is a single point
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `capsule/representsa_` at `point`, tolerance `0`: no direction and no radius. -/
def Capsule.representsa_point (C : Capsule n) : Prop := C.g = 0 ∧ C.r = 0

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
