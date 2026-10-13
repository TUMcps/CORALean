import CORALean.ContDynamics.LinParamSys.LinParamSys
import CORALean.ContDynamics.LinearSys.MatExp.Operations.AdmissibleOrderFloat
import CORALean.ContDynamics.LinearSys.MatExp.Operations.NormUpperBoundFloat
import CORALean.ContSet.Interval.Float.Operations.Smul

/-!
# A Taylor order admissible at every member, searched in floats

`LinearSys.reachOrderFloat` at the system's interval matrix: the first order
from `max η 2` that `MatExp.admissibleOrder` certifies against the float norm
bound of `[tLo, tHi] · sys.A`. `reachOrderFloat_spec` is what it guarantees.
-/

-- Authors:       Claude Opus 5.5
-- Written:       01-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Float

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The first order from `max η 2` the float remainder bound at `[tLo, tHi] · sys.A`
admits, or `none` if none of the next `4096` does. -/
def LinParamSys.reachOrderFloat (sys : LinParamSys (fun m n => Interval (Mat 𝕋 m n)) n)
    (tLo tHi : 𝕋) (η : ℕ) : Option ℕ :=
  let nrm := MatExp.normUpperBound (Interval.smul tLo tHi sys.A)    -- ≥ ‖t A‖, every A ∈ sys.A
  MatExp.admissibleOrder nrm (max η 2) 4096                          -- η + 2 ≥ 2 nrm, from max η 2

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
