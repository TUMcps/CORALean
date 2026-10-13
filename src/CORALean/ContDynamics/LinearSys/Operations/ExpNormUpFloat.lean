import CORALean.ContDynamics.LinearSys.LinearSys
import CORALean.ContDynamics.LinearSys.MatExp.Operations.NormUpperBoundFloat
import CORALean.ContSet.Interval.Float.Operations.Point
import CORALean.ContSet.Interval.Float.Operations.Smul
import CORALean.Global.Float.Exp

/-!
# `e^{r‖A‖}` from above, in floats

The scalar exponential the step's error estimates are stated in, at `nrm`, the float bound
`MatExp.normUpperBound` on `‖r A‖` the step's enclosures are taken at. `expUp p` is sound for
`nrm ≤ 2^p / 2`; at an order `η` the float enclosures admit, `nrm ≤ (η + 2)/2`, so
`p = log₂(η + 2) + 5` is enough, and halves the argument to under `1/32` before squaring.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       08-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Float

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `e^{nrm}` from above, `nrm ≥ ‖r A‖` the float norm bound at `[r, r] · A`. -/
def LinearSys.expNormUpFloat (sys : LinearSys 𝕋 n) (r : 𝕋) (η : ℕ) : 𝕋 :=
  let nrm := MatExp.normUpperBound (Interval.smul r r (Interval.point sys.A))   -- ≥ ‖r A‖
  expUp (Nat.log2 (η + 2) + 5) nrm                                              -- ≥ e^{nrm}

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
