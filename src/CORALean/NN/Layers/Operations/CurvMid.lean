module

public import CORALean.NN.Layers.Operations.CurvHi
public import CORALean.NN.Layers.Operations.CurvLo

@[expose] public section

/-!
# The offset a derivative bracket stores

Any value between the two ends would do as the offset, the error being measured from the one
stored; the midpoint makes the error smallest, and its own rounding costs nothing.
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-September-2026
-- Last update:   23-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Float Float.FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The midpoint of the two ends, the offset `Relaxation.ofDeriv` stores. -/
def Relaxation.curvMid (E : Enclosure 𝕋) (lo hi lam : 𝕋 → 𝕋 → 𝕋) (l u : 𝕋) : 𝕋 :=
  half (addUp (Relaxation.curvLo E lo lam l u) (Relaxation.curvHi E hi lam l u))

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
