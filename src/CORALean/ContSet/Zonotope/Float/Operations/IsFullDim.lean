module

public import CORALean.ContSet.Zonotope.Float.Operations.IsFullDimWith
public import CORALean.ContSet.Zonotope.Float.Operations.RightInvCandidate

@[expose] public section

/-!
# `Zonotope.isFullDim`, over a floating-point scalar

`Zonotope.isFullDimWith` at the default candidate right inverse `Zonotope.rightInvCandidate`, the
Gram-matrix inverse of the generators, which needs no help from the caller. Only `true` is
certain.
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

def Zonotope.isFullDim (Z : Zonotope (Vec 𝕋 n)) : Bool :=
  Z.isFullDimWith (Zonotope.rightInvCandidate fun i j => Z.G j i)

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
