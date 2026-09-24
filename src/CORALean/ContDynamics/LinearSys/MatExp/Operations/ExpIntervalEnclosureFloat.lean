import CORALean.ContDynamics.LinearSys.MatExp.Operations.ExpIntervalTaylorFloat
import CORALean.ContDynamics.LinearSys.MatExp.Operations.ExpRemainderBoundFloat
import CORALean.ContDynamics.LinearSys.MatExp.Operations.NormUpperBoundFloat

/-!
# `MatExp.expIntervalEnclosure`, over a floating-point scalar

`Real.MatExp.expIntervalEnclosure` rounded: the float Taylor box, `expUp`ended
by the remainder bound taken at `normUpperBound`, exactly as the exact layer
widens by `expRemainderBound` at `A.absMax`.
-/

-- Authors:       Tobias Ladner
-- Written:       24-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def MatExp.expIntervalEnclosure (A : Interval (Mat 𝕋 n n)) (η : ℕ) : Interval (Mat 𝕋 n n) where
  inf := fun i j => subDown ((MatExp.expIntervalTaylor A η).inf i j)
    (MatExp.expRemainderBound (MatExp.normUpperBound A) η)
  sup := fun i j => addUp ((MatExp.expIntervalTaylor A η).sup i j)
    (MatExp.expRemainderBound (MatExp.normUpperBound A) η)

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
