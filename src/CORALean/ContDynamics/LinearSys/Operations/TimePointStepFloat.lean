import CORALean.ContDynamics.LinearSys.Operations.ExpIntervalFloat
import CORALean.ContSet.Zonotope.Float.Instances

/-!
# One step of the homogeneous flow at its end, as a float zonotope

`timePointStep` without an input, computed in `𝕋`: `[e^{AΔt}] R`, the float
enclosure `expIntervalFloat` at the point range `[Δt, Δt]` applied by
`Zonotope.mtimesIntervalMat`, which carries the error box through the interval
matrix as a box. The step `reachFloat` iterates.
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

/-- `[e^{AΔt}] R` at Taylor order `η`. -/
def LinearSys.timePointStepFloat (sys : LinearSys 𝕋 n) (Δt : 𝕋) (η : ℕ) (R : Zonotope 𝕋 n) :
    Zonotope 𝕋 n :=
  let eAΔt := sys.expIntervalFloat Δt Δt η                                  -- [e^{AΔt}]
  Mtimes.mtimes (𝕄 := fun m n => Interval (Mat 𝕋 m n)) eAΔt R              -- [e^{AΔt}] R

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
