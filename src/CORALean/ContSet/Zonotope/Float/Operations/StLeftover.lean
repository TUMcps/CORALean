import CORALean.ContSet.Zonotope.Float.Operations.StGamma
import CORALean.ContSet.Zonotope.Float.Operations.StBeta
import CORALean.ContSet.Zonotope.Float.Operations.PointLo
import CORALean.ContSet.Zonotope.Float.Operations.PointHi
import CORALean.ContSet.Zonotope.Float.Operations.EntryDeviation
import CORALean.ContSet.Zonotope.Float.Operations.MulResidual
import CORALean.ContSet.Zonotope.Float.Operations.ErrBound

/-!
# `Zonotope.stLeftover`

What everything the coefficients leave over costs in one entry, rounded up.
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

def Zonotope.stLeftover (Z₂ Z₁ : Zonotope 𝕋 n) (H : Mat 𝕋 Z₂.h n) (i : Fin n) : 𝕋 :=
  addUp (addUp
    (Zonotope.entryDeviation Z₁.c Z₂.E.inf (Z₂.pointLo (Z₂.stBeta Z₁ H))
      (Z₂.pointHi (Z₂.stBeta Z₁ H)) i)
    (sumUp fun j => Zonotope.mulResidual (fun i j => Z₁.G j i) (fun i j => Z₂.G j i)
      (Z₂.stGamma Z₁ H) i j))
    (Zonotope.errBound Z₁.E i)

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
