import CORALean.ContDynamics.NonlinearSys.Operations.LinPointFloat
import CORALean.ContDynamics.NonlinearSys.Operations.RelinStepAtFloat

/-!
# One step of the float re-linearization loop, at the half-step point

`relinStepAtFloat` at the expansion point `linPointFloat` computes: the centre of the set the
step starts from, carried half a step along the field.
-/

-- Authors:       Claude Opus 5.5
-- Written:       01-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Float FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] [ToRat 𝕋] {n m : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `(R(τ_k), R(t_{k+1}))` from `R = R(t_k)` under inputs in `U`, or `none` if the
region check or the linear step fails: `relinStepAtFloat` at `x✱ = linPointFloat`. -/
def NonlinearSys.FloatModel.relinStepFloat (fm : NonlinearSys.FloatModel 𝕋 n m)
    (U : Zonotope (Vec 𝕋 m)) (options : LinearSys.ReachOptions 𝕋) (R : Zonotope (Vec 𝕋 n)) :
    Option (Zonotope (Vec 𝕋 n) × Zonotope (Vec 𝕋 n)) :=
  let xs := (fm.linPointFloat options.Δt R U).1                -- 3. x✱, the half-step point
  fm.relinStepAtFloat U options R xs

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
