import CORALean.ContSet.Taylm.Float.Operations.Taylor
import CORALean.ContSet.Taylm.Float.Operations.SqrtCoef
import CORALean.ContSet.Taylm.Float.Operations.SqrtBound

/-!
# `Taylm.sqrt`

The exact layer's `sqrt` with every number enclosed: the coefficients `Taylm.sqrtCoef` at the
centre, the Lagrange bound `Taylm.sqrtBound` at the smaller of the centre and the bottom of the
range, where `√⁽ᴺ⁺¹⁾` is largest. `q` is the precision of the square root.
-/

-- Authors:       Tobias Ladner
-- Written:       03-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def Taylm.sqrt (q : ℕ) (T : Taylm 𝕋 n) : Taylm 𝕋 n :=
  T.taylor T.constCoef (fun k => (Taylm.sqrtCoef q T.constCoef k).1)
    (fun k => (Taylm.sqrtCoef q T.constCoef k).2)
    (Taylm.sqrtBound q (minimum T.constCoef T.bounds.1) T.maxOrder)

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
