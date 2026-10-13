import CORALean.ContSet.Zonotope.Float.Operations.IsFullDimWith
import CORALean.ContSet.Zonotope.Float.Operations.RightInvCandidate

/-!
# `Zonotope.isFullDim`, over a floating-point scalar

`Zonotope.isFullDimWith` at the default candidate right inverse `Zonotope.rightInvCandidate`, the
Gram-matrix inverse of the generators, which needs no help from the caller. Only `true` is
certain.
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

def Zonotope.isFullDim (Z : Zonotope (Vec 𝕋 n)) : Bool :=
  Z.isFullDimWith (Zonotope.rightInvCandidate fun i j => Z.G j i)

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
