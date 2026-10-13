import CORALean.ContSet.HPolytope.Float.Operations.OfBounds
import CORALean.ContSet.ContSet.Float.Operations.SupportBound

/-!
# `HPolytope.mtimesOf`

What a float halfspace description cannot do exactly: the map is a float
matrix, so a direction on the target is pulled back through what that matrix
denotes.
-/

-- Authors:       Tobias Ladner
-- Written:       02-September-2026
-- Last update:   05-September-2026
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open Matrix FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {q n p : ℕ}
variable {P : HPolytope 𝕋 (Vec 𝕋 n)}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The map is a float matrix, so a direction on the target is pulled back
through what that matrix denotes. -/
def HPolytope.mtimesOf (M : Mat 𝕋 p n) (Aq : Mat 𝕋 q p)
    (u : ∀ i, FloatBound 𝕋 P.construct ((rowLin Aq i).comp (mulVecLin (toRealMat M)))) :
    HPolytope 𝕋 (Vec 𝕋 p) :=
  HPolytope.ofBounds Aq fun i => FloatBound.image _ (u i)

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
