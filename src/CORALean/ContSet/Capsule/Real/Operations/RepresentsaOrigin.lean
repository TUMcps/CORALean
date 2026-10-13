import CORALean.ContSet.Capsule.Real.Operations.RepresentsaPoint

/-!
# `Capsule.representsa_origin`

CORA's `@capsule/representsa_.m` at `origin`: `isPoint && all(withinTol(C.c, 0, tol))`, here at
tolerance `0`.
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `capsule/representsa_` at `origin`, tolerance `0`: a point whose centre is `0`. -/
def Capsule.representsa_origin (C : Capsule n) : Prop := C.c = 0 ∧ C.representsa_point

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
