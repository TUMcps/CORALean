import CORALean.ContSet.Zonotope.Float.Operations.RotMat
import CORALean.ContSet.Zonotope.Float.Operations.MtimesIntervalMat

/-!
# `Zonotope.rotate`

CORA's `@zonotope/rotate`, `rotMat * Z`, with the rotation known only to within the sine and
cosine enclosures: the interval matrix `rotMat` times the zonotope, `mtimesIntervalMat`.
-/

-- Authors:       Tobias Ladner
-- Written:       02-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

variable {𝕋 : Type} [FloatOps 𝕋]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `zonotope/rotate`. -/
def Zonotope.rotate (p : ℕ) {n : ℕ} (Z : Zonotope 𝕋 n) (i j : Fin n) (angle : 𝕋) :
    Zonotope 𝕋 n :=
  Zonotope.mtimesIntervalMat (rotMat p n i j angle) Z

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
