import CORALean.ContSet.PolyZonotope.Float.Operations.IsFullDimWith
import CORALean.ContSet.Zonotope.Float.Operations.RightInvCandidate

/-!
# `PolyZonotope.isFullDim`, over a floating-point scalar

`PolyZonotope.isFullDimWith` at the default candidate right inverse of the independent generators
(`Zonotope.rightInvCandidate`). Only `true` is certain.
-/

-- Authors:       Tobias Ladner
-- Written:       04-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def PolyZonotope.isFullDim (pZ : PolyZonotope (Vec 𝕋 n)) : Bool :=
  pZ.isFullDimWith (Zonotope.rightInvCandidate fun i j => pZ.GI j i)

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
