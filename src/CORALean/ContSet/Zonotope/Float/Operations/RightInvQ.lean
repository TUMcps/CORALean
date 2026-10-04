import CORALean.ContSet.Zonotope.Float.Operations.RightInvResidual

/-!
# `Zonotope.rightInvQ`

An upper bound on the largest absolute row sum of `1 - G H`, rounded up: the certificate that a
candidate right inverse `H` is good enough (`Zonotope.rightInv_reach`) when it is at most one half.
-/

-- Authors:       Tobias Ladner
-- Written:       04-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n h : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def Zonotope.rightInvQ (G : Mat 𝕋 n h) (H : Mat 𝕋 h n) : 𝕋 :=
  maximumOver fun i => sumUp fun j => Zonotope.rightInvResidual G H i j

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
