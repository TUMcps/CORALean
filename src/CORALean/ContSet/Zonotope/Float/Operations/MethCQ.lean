import CORALean.ContSet.Zonotope.Float.Operations.MethCResidual

/-!
# `Zonotope.methCQ`

The certificate for a candidate inverse: the largest absolute row sum of
`methCResidual`, rounded up. If it is at most one half, `H` is close enough to the inverse of
`P` that `P` is invertible and its coordinates are bounded (`Zonotope.basis_reach`).
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

/-- An upper bound on the largest absolute row sum of `1 - H P`. -/
def Zonotope.methCQ (H P : Mat 𝕋 n n) : 𝕋 :=
  maximumOver fun i => sumUp fun j => Zonotope.methCResidual H P i j

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
