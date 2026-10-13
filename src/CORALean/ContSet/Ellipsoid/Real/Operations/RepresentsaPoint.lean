import CORALean.ContSet.Ellipsoid.Real.Ellipsoid

/-!
# `Ellipsoid.representsa_point`

CORA's `@ellipsoid/representsa_` at type `point` with tolerance `0`: the shape matrix vanishes,
`Q = 0`. CORALean stores the generator matrix, and `Q = G Gᵀ = 0` iff `G = 0`.
-/

-- Authors:       Claude Opus 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `ellipsoid/representsa_` at `point`. -/
def Ellipsoid.representsa_point (E : Ellipsoid n) : Prop := E.G = 0

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
