module

public import CORALean.ContSet.Zonotope.Float.Operations.RotMat
public import CORALean.ContSet.Zonotope.Float.Operations.MtimesIntervalMat

@[expose] public section

/-!
# `Zonotope.rotate`

CORA's `@zonotope/rotate`, `rotMat * Z`, with the rotation known only to within the sine and
cosine enclosures: the interval matrix `rotMat` times the zonotope, `mtimesIntervalMat`.
-/

-- Authors:       Claude Opus 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

variable {𝕋 : Type} [FloatOps 𝕋]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `zonotope/rotate`. -/
def Zonotope.rotate (p : ℕ) {n : ℕ} (Z : Zonotope (Vec 𝕋 n)) (i j : Fin n) (angle : 𝕋) :
    Zonotope (Vec 𝕋 n) :=
  Zonotope.mtimesIntervalMat (rotMat p n i j angle) Z

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
