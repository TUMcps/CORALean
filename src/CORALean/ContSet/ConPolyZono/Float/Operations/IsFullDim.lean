import CORALean.ContSet.ConPolyZono.Float.Operations.IsFullDimWith
import CORALean.ContSet.Zonotope.Float.Operations.RightInvCandidate

/-!
# `ConPolyZono.isFullDim`, over a floating-point scalar

`ConPolyZono.isFullDimWith` at the default candidate right inverse of the independent generators
(`Zonotope.rightInvCandidate`). Only `true` is certain.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def ConPolyZono.isFullDim (cPZ : ConPolyZono 𝕋 (Vec 𝕋 n)) : Bool :=
  cPZ.isFullDimWith (Zonotope.rightInvCandidate fun i j => cPZ.GI j i)

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
