module

public import CORALean.ContDynamics.LinParamSys.LinParamSys
public import CORALean.ContDynamics.LinearSys.MatExp.Operations.ExpMatZonoEnclosureFloat
public import CORALean.ContDynamics.LinearSys.MatExp.Operations.MatZonoCorrectionMatrixFloat
public import CORALean.ContSet.Zonotope.Float.Instances
public import CORALean.ContSet.Zonotope.Float.Operations.MatSmul

@[expose] public section

/-!
# One step of the homogeneous flow at a float matrix zonotope, as a float zonotope

`LinParamSys.timeIntervalStepZono` computed in `𝕋`, CORA's `initReach` with `obj.A` a
`matZonotope`: `linComb(R, e^{[A]Δt} R) ⊕ F R`, the exponential kept as a matrix
zonotope (`expMatZonoEnclosure` at `Δt • A`, `matSmul` at the point range `[Δt, Δt]`),
and the correction `F` the boxed powers give (`matZonoCorrectionMatrix`). `Δt` is a
float and its own value is the step.
-/

-- Authors:       Claude Opus 5.5
-- Written:       09-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Float

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `linComb(R, e^{[A]Δt} R) ⊕ F R` over every `A` in the matrix zonotope `sys.A`, at
Taylor order `η`. -/
def LinParamSys.timeIntervalStepZonoFloat
    (sys : LinParamSys (fun m n => Zonotope (Mat 𝕋 m n)) n) (Δt : 𝕋) (η : ℕ)
    (R : Zonotope (Vec 𝕋 n)) : Zonotope (Vec 𝕋 n) :=
  let Ar := Zonotope.matSmul Δt Δt sys.A                                -- A * stepSize
  let eAr := MatExp.expMatZonoEnclosure Ar η                             -- mappingMatrixSet
  let F := MatExp.matZonoCorrectionMatrix sys.A Δt η                     -- priv_tie's F
  LinComb.linComb R (Mtimes.mtimes (𝕄 := fun m n => Zonotope (Mat 𝕋 m n))
    (S := fun k => Zonotope (Vec 𝕋 k)) eAr R) ⊞
    Mtimes.mtimes (𝕄 := fun m n => Interval (Mat 𝕋 m n))  -- linComb(R, e R) ⊕ F R
      (S := fun k => Zonotope (Vec 𝕋 k)) F R

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
