import CORALean.ContSet.VPolytope.Float.Operations.NominalBoundNegProj
import CORALean.ContSet.Interval.Float.Operations.BoundNegProj

/-!
# `VPolytope.boundNegProj`

The nominal bound and the error box's own, added.
-/

-- Authors:       Tobias Ladner
-- Written:       02-September-2026
-- Last update:   05-September-2026
-- Last revision: ---

namespace CORALean.Float

open FloatOps SoundFloatArithmetic InflatedContSet

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}

def VPolytope.boundNegProj (P : VPolytope 𝕋 n) (j : Fin n) :
    FloatBound 𝕋 P.construct (-LinearMap.proj j) :=
  InflatedContSet.boundOfParts (P.nominalBoundNegProj j) (P.E.boundNegProj j)

end CORALean.Float
