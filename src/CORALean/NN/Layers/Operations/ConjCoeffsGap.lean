import CORALean.NN.Layers.Operations.ConjCoeffsDown
import CORALean.NN.Layers.Operations.ConjCoeffsUp

/-!
# How far the stored conjugated coefficients can be from the exact ones

Each exact coefficient lies between its two roundings and the stored one is the upper, so the
difference of the two bounds the deviation, rounded up.
-/

-- Authors:       Tobias Ladner
-- Written:       12-October-2026
-- Last update:   12-October-2026
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Float Float.FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {m : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- An upper bound on the distance of each stored coefficient from the exact one. -/
def conjCoeffsGap (A B : ScaleRounding 𝕋) (c : 𝕋) (p : Fin (m + 1) → 𝕋) : Fin (m + 1) → 𝕋 :=
  fun i => subUp (conjCoeffsUp A B c p i) (conjCoeffsDown A B c p i)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
