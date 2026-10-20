module

public import CORALean.ContDynamics.NonlinearSys.Operations.LinPointFloat
public import CORALean.ContDynamics.NonlinearSys.Operations.RelinRunAtFloat
public import CORALean.ContDynamics.NonlinearSys.Operations.RelinStepFloat

@[expose] public section

/-!
# The float re-linearization loop, at the half-step point

`relinRunAtFloat` with each step linearized at `linPointFloat` of its start set.

## Inputs
* `fm` – float model
* `U` – input zonotope
* `options` – reachability options

## Output
* the time-interval sets of the steps, or none
-/

-- Authors:       Claude Opus 5.5
-- Written:       01-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Float

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] [ToRat 𝕋] {n m : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `R(τ_0), …, R(τ_{k-1})` of `k` re-linearized steps from `R`, or `none` if
one of them fails: `relinRunAtFloat` at `x✱ = linPointFloat`. -/
def NonlinearSys.FloatModel.relinRunFloat (fm : NonlinearSys.FloatModel 𝕋 n m)
    (U : Zonotope (Vec 𝕋 m)) (options : LinearSys.ReachOptions 𝕋) :
    ℕ → Zonotope (Vec 𝕋 n) → Option (List (Zonotope (Vec 𝕋 n))) :=
  fm.relinRunAtFloat U options fun R => (fm.linPointFloat options.Δt R U).1

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
