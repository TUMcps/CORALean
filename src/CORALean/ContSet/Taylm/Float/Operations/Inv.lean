import CORALean.ContSet.Taylm.Float.Operations.Taylor
import CORALean.ContSet.Taylm.Float.Operations.InvCoef
import CORALean.ContSet.Taylm.Float.Operations.InvBound

/-!
# `Taylm.inv`, over a floating-point scalar

`1/x` through the Taylor model of `taylor`, as over ℝ: the coefficients at the centre
(`invCoef`), and the remainder from the derivative bound at the distance `m` of the hull of the
centre and the range from zero, `max (min c lo) (-max c hi)` (`invBound`). Sound where `m > 0`.
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

def Taylm.inv (T : Taylm 𝕋 n) : Taylm 𝕋 n :=
  T.taylor T.constCoef (fun k => (Taylm.invCoef T.constCoef k).1)
    (fun k => (Taylm.invCoef T.constCoef k).2)
    (Taylm.invBound (maximum (minimum T.constCoef T.bounds.1)
      (neg (maximum T.constCoef T.bounds.2))) T.maxOrder)

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
