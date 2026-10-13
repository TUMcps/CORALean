import CORALean.ContSet.VPolytope.Float.Operations.NominalBoundProj
import CORALean.ContSet.Interval.Float.Operations.BoundProj

/-!
# `VPolytope.boundProj`

The nominal bound and the error box's own, added.
-/

-- Authors:       Claude Opus 5
-- Written:       02-September-2026
-- Last update:   05-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic InflatedContSet

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def VPolytope.boundProj (P : VPolytope (Vec 𝕋 n)) (j : Fin n) :
    FloatBound 𝕋 P.construct (LinearMap.proj j) :=
  InflatedContSet.boundOfParts (P.nominalBoundProj j) (P.E.boundProj j)

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
