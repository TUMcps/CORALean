import CORALean.ContDynamics.LinearSys.MatExp.Operations.IntervalCorrectionMatrixFloat
import CORALean.ContDynamics.LinearSys.Operations.ExpIntervalFloat
import CORALean.ContSet.Zonotope.Float.Instances

/-!
# One step of the homogeneous flow as a float zonotope

`timeIntervalStep` computed in `𝕋`: `R(τ) = linComb(R, [e^{AΔt}] R) ⊕ [F] R`,
both matrices float interval enclosures at the stored `A` — `expIntervalFloat`
at the point range `[Δt, Δt]`, and `MatExp.intervalCorrectionMatrix`. Each
product is `Zonotope.mtimesIntervalMat`, which multiplies the error box by the
interval matrix too, so rounding stays in the box and is never folded into a
generator.

`Δt` is a float and its own value is the step: nothing rounds the time here.
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

/-- `linComb(R, [e^{AΔt}] R) ⊕ [F] R` at Taylor order `η`. -/
def LinearSys.timeIntervalStepFloat (sys : LinearSys 𝕋 n) (Δt : 𝕋) (η : ℕ) (R : Zonotope 𝕋 n) :
    Zonotope 𝕋 n :=
  let eAΔt := sys.expIntervalFloat Δt Δt η                                  -- [e^{AΔt}]
  let F := MatExp.intervalCorrectionMatrix (Interval.point sys.A) Δt η      -- [F]
  LinComb.linComb R (Mtimes.mtimes (𝕄 := fun m n => Interval (Mat 𝕋 m n)) eAΔt R) ⊞
    Mtimes.mtimes (𝕄 := fun m n => Interval (Mat 𝕋 m n)) F R          -- linComb(R, e R) ⊕ F R

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
