module

public import CORALean.ContSet.Taylm.Float.Operations.Taylor
public import CORALean.ContSet.Taylm.Float.Operations.InvCoef
public import CORALean.ContSet.Taylm.Float.Operations.InvBound

@[expose] public section

/-!
# `Taylm.inv`, over a floating-point scalar

`1/x` through the Taylor model of `taylor`, as over ℝ: the coefficients at the center
(`invCoef`), and the remainder from the derivative bound at the distance `m` of the hull of the
center and the range from zero, `max (min c lo) (-max c hi)` (`invBound`). Sound where `m > 0`.
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   14-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def Taylm.inv (T : Taylm 𝕋 n) : Taylm 𝕋 n :=
  T.taylor T.constCoef (fun k => (Taylm.invCoef T.constCoef k).inf)
    (fun k => (Taylm.invCoef T.constCoef k).sup)
    (Taylm.invBound (maximum (minimum T.constCoef T.bounds.inf)
      (neg (maximum T.constCoef T.bounds.sup))) T.maxOrder)

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
