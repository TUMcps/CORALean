import CORALean.ContSet.VPolytope.Float.Operations.IsFullDimWith
import CORALean.ContSet.Zonotope.Float.Operations.RightInvCandidate

/-!
# `VPolytope.isFullDim`, over a floating-point scalar

`VPolytope.isFullDimWith` at the default candidate right inverse of the bordered vertex matrix
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

def VPolytope.isFullDim (P : VPolytope (Vec 𝕋 n)) : Bool :=
  P.isFullDimWith (Zonotope.rightInvCandidate P.bordered)

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
