module

public import CORALean.ContDynamics.LinearSys.MatExp.Operations.IntervalCorrectionMatrixFloat
public import CORALean.ContDynamics.LinearSys.Operations.ExpIntervalFloat
public import CORALean.ContSet.Zonotope.Float.Instances

@[expose] public section

/-!
# One step of the homogeneous flow as a float zonotope

`timeIntervalStep` computed in `𝕋`: `R(τ) = linComb(R, [e^{AΔt}] R) ⊕ [F] R`,
both matrices float interval enclosures at the stored `A` — `expIntervalFloat`
at the point range `[Δt, Δt]`, and `MatExp.intervalCorrectionMatrix`. Each
product is `Zonotope.mtimesIntervalMat`, which multiplies the error box by the
interval matrix too, so rounding stays in the box and is never folded into a
generator.

`Δt` is a float and its own value is the step: nothing rounds the time here.

## Inputs
* `sys` – linear system
* `Δt` – float step length
* `η` – Taylor order
* `R` – float state zonotope

## Output
* float zonotope over the whole step
-/

-- Authors:       Claude Opus 5.5
-- Written:       25-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Float

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `linComb(R, [e^{AΔt}] R) ⊕ [F] R` at Taylor order `η`. -/
def LinearSys.timeIntervalStepFloat (sys : LinearSys 𝕋 n) (Δt : 𝕋) (η : ℕ)
    (R : Zonotope (Vec 𝕋 n)) :
    Zonotope (Vec 𝕋 n) :=
  let eAΔt := sys.expIntervalFloat Δt Δt η                                  -- [e^{AΔt}]
  let F := MatExp.intervalCorrectionMatrix (Interval.point sys.A) Δt η      -- [F]
  LinComb.linComb R (Mtimes.mtimes (𝕄 := ℐ[𝕋])
    (S := 𝒵[𝕋]) eAΔt R) ⊞
    Mtimes.mtimes (𝕄 := ℐ[𝕋])  -- linComb(R, e R) ⊕ F R
      (S := 𝒵[𝕋]) F R

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
