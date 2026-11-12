module

public import CORALean.ContDynamics.NonlinearSys.Operations.LinReachLoopFloat
public import CORALean.ContDynamics.Reach.Operations.Steps
public import CORALean.Global.StepOf

@[expose] public section

/-!
# Nonlinear reachability in floats with CORA's error loop: `nonlinearSys/reach` at `alg = 'lin'`

`ẋ = f(x, u)`, `u(t) ∈ U` arbitrary in time, from `X₀`, computed in `𝕋` from a `FloatHessModel`:
`N = (tFinal - tStart) / Δt` steps of `linReachLoopFloat` (`step_linReachLoopRunFloat`), each
returning its set over the whole step and handing its abstraction error to the next, which
guesses `1.1` times it. The first step guesses from zero, as `Rstart.error` does in CORA. It is
`reachAlgFloat` at `'lin'` with the loop in place of the checked region, so it takes steps the
region check would refuse. `none` is returned where `N` is no natural number or a step fails.

## Inputs
* `fm` – float Hessian model
* `params` – reachability parameters
* `options` – reachability options
* `enlarge` – enlargement of the error, CORA's `1.1`
* `fuel` – iteration bound of each step's loop
* `maxError` – largest admissible error, if any
* `step` – linear step

## Output
* the time-interval sets of all steps, or none
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       12-November-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Float FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] [ToRat 𝕋] {n m : ℕ}


-- ------------------------------------------  STEPS  ------------------------------------------- --

/-- `R(τ_0), …, R(τ_{k-1})` of `k` loop steps from `R`, each guessing from the last one's error
`err`, or `none` if one of them fails. -/
@[step_of NonlinearSys.FloatHessModel.reachLoopFloat]
def NonlinearSys.FloatHessModel.step_linReachLoopRunFloat (fm : NonlinearSys.FloatHessModel 𝕋 n m)
    (U : Zonotope (Vec 𝕋 m)) (options : LinearSys.ReachFloatOptions 𝕋) (enlarge : 𝕋) (fuel : ℕ)
    (maxError : Option (Vec 𝕋 n)) (step : NonlinearSys.LinearStep) :
    ℕ → Zonotope (Vec 𝕋 n) → Vec 𝕋 n → Option (List (Zonotope (Vec 𝕋 n)))
  | 0, _, _ => some []
  | k + 1, R, err => do
    let S ← fm.linReachLoopFloat U options enlarge fuel R err maxError step  -- (R(τ), R(t+Δt), err)
    let rest ← fm.step_linReachLoopRunFloat U options enlarge fuel maxError step k S.2.1 S.2.2
    pure (S.1 :: rest)                                              -- the steps after it


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The windows `R(τ_0), …, R(τ_{N-1})` of `ẋ = f(x, u)` from `X₀` under inputs in `U`, each step's
abstraction error bounded by CORA's loop. -/
def NonlinearSys.FloatHessModel.reachLoopFloat (fm : NonlinearSys.FloatHessModel 𝕋 n m)
    (params : Reach.InputParams (Zonotope (Vec 𝕋 n)) (Zonotope (Vec 𝕋 m)) ℚ)
    (options : LinearSys.ReachFloatOptions 𝕋) (enlarge : 𝕋) (fuel : ℕ)
    (maxError : Option (Vec 𝕋 n) := none)
    (step : NonlinearSys.LinearStep := .reachFloatInput) :
    Option (List (Zonotope (Vec 𝕋 n))) := do
  let X₀ := params.X₀                                               -- the paper's symbols
  let Δt := options.Δt
  let N ← Reach.steps params.tStart params.tFinal (ToRat.toRat Δt)  -- (tFinal - tStart) / Δt ∈ ℕ
  fm.step_linReachLoopRunFloat params.U options enlarge fuel maxError step N X₀
    (fun _ => zero)                                                 -- Rstart.error = zeros(n,1)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
