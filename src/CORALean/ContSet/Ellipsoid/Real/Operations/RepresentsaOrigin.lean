import CORALean.ContSet.Ellipsoid.Real.Operations.RepresentsaPoint

/-!
# `Ellipsoid.representsa_origin`

CORA's `@ellipsoid/representsa_` at type `origin` with tolerance `0`: a point at `q = 0`.
-/

-- Authors:       Tobias Ladner
-- Written:       02-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `ellipsoid/representsa_` at `origin`. -/
def Ellipsoid.representsa_origin (E : Ellipsoid n) : Prop := E.q = 0 ∧ E.representsa_point

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
