import CORALean.ContDynamics.LinearSys.LinearSys
import CORALean.ContDynamics.LinearSys.MatExp.Operations.AccurateOrderFloat
import CORALean.ContDynamics.LinearSys.MatExp.Operations.NormUpperBoundFloat
import CORALean.ContSet.Interval.Float.Operations.Point
import CORALean.ContSet.Interval.Float.Operations.Smul

/-!
# A Taylor order for a later window, as accurate as the step's

`e^{A t}` at a time range `[tLo, tHi]` far from zero has a norm `‖A t‖` the
step's order is not admissible at, and an order merely admissible there has a
remainder that grows like `‖A t‖^{η+1}/(η+1)!` at `η ≈ 2‖A t‖`. So a window
takes `MatExp.accurateOrder`: the first order from `max η 2` that is admissible
at `[tLo, tHi] · A` and whose remainder bound is at most the one the step itself
pays at `[Δt, Δt] · A` and order `η` — every window's matrix is then enclosed as
tightly as the step's is. `none` after `4096` orders.
-/

-- Authors:       Tobias Ladner
-- Written:       25-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Float

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The first order from `max η 2` admissible at `[tLo, tHi] · A` with a remainder
bound no larger than the step's at `Δt` and `η`. -/
def LinearSys.windowOrderFloat (sys : LinearSys 𝕋 n) (Δt tLo tHi : 𝕋) (η : ℕ) : Option ℕ :=
  let nrmΔt := MatExp.normUpperBound (Interval.smul Δt Δt (Interval.point sys.A))  -- ≥ ‖Δt A‖
  let tol := MatExp.expRemainderBound nrmΔt η                          -- the step's remainder
  let nrm := MatExp.normUpperBound (Interval.smul tLo tHi (Interval.point sys.A))  -- ≥ ‖t A‖
  MatExp.accurateOrder nrm tol (max η 2) 4096                         -- admissible, within tol

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
