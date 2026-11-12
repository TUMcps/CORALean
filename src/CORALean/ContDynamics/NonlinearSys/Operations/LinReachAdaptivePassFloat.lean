module

public import CORALean.ContDynamics.LinearSys.Operations.CanonicalFloat
public import CORALean.ContDynamics.LinearSys.Operations.ErrorSolutionAdaptiveFloat
public import CORALean.ContDynamics.NonlinearSys.Definitions.LinReachAdaptiveState
public import CORALean.ContDynamics.NonlinearSys.Definitions.LinReachAdaptivePass
public import CORALean.ContDynamics.NonlinearSys.Definitions.LinReachAdaptiveLoop
public import CORALean.ContDynamics.NonlinearSys.Operations.AbstrErrAdaptiveFloat
public import CORALean.ContDynamics.NonlinearSys.Operations.LinPointFloat
public import CORALean.ContDynamics.NonlinearSys.Operations.LinearizeFloat
public import CORALean.ContDynamics.NonlinearSys.Operations.OneStepFloat
public import CORALean.ContSet.Interval.Float.Operations.Basic

@[expose] public section

/-!
# One pass of CORA's `linReach_adaptive` at a fixed `Δt`, repaired, in floats

The body of `linReach_adaptive`'s outer loop at `alg = 'lin'` up to `Rerror`: `linearize`, and the
loop "until the actual abstraction error is smaller than the estimated": `Rmax` is the window of
the linearized system with input `f0 ⊕ B(U - p.u) ⊕ [-error_adm, error_adm]` (CORA's `Rlinti +
RallError`), `VerrorDyn` the error over it, accepted once `trueError ≤ error_adm`, else
`error_adm = 1.1 trueError`, given up from the third pass if `perfIndCurr` grows. The step's sets
are one linear step with input `f0 ⊕ B(U - p.u) ⊕ VerrorDyn`: CORA's `Rlinti +
errorSolution_adaptive(VerrorDyn)` misses the window's start once `VerrorDyn` does not hold the
origin (tensor order 3). `errorSolution_adaptive` still gives `abstrerr`, read by the tuning only.

## Inputs
* `fm` – float Hessian model
* `κ` – tensor order
* `U` – input zonotope
* `options` – reachability options
* `enlarge` – enlargement of the admissible error
* `redFactor` – reduction factor
* `p` – square root precision
* `fuel` – iteration bound
* `R` – start zonotope
* `errorAdm` – initial admissible error
* `step` – linear step

## Output
* the sets of the pass and what the tuning reads, or none
-/

-- Authors:       Claude Opus 5.5
-- Written:       10-November-2026
-- Last update:   11-November-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Float FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] [ToRat 𝕋] {n m : ℕ}


-- ------------------------------------------  STEPS  ------------------------------------------- --

/-- The inner loop: `(Rmax + p.x, VerrorDyn, trueError)` of the first pass whose `trueError` is
at most its `error_adm`, or none once it gives up or `fuel` runs out. -/
@[step_of NonlinearSys.FloatHessModel.linReachAdaptivePassFloat]
def NonlinearSys.FloatHessModel.step_abstrErrLoopAdaptive (fm : NonlinearSys.FloatHessModel 𝕋 n m)
    (κ : ℕ) (A : Mat 𝕋 n n) (B : Mat 𝕋 n m) (xs : Vec 𝕋 n) (Vbase R : Zonotope (Vec 𝕋 n))
    (U : Zonotope (Vec 𝕋 m)) (options : LinearSys.ReachFloatOptions 𝕋) (enlarge redFactor : 𝕋)
    (p : ℕ) (step : NonlinearSys.LinearStep) : ℕ → ℕ → 𝕋 → Vec 𝕋 n →
      Option (Zonotope (Vec 𝕋 n) × Zonotope (Vec 𝕋 n) × Vec 𝕋 n)
  | 0, _, _, _ => none
  | fuel + 1, perfIndCounter, perfIndPrev, errorAdm =>
    let Verror := (⟨-errorAdm, errorAdm⟩ : Interval (Vec 𝕋 n)).zonotope  -- zonotope(0,diag(..))
    match NonlinearSys.oneStepFloat A xs (Vbase ⊞ Verror) R options  -- Rmax = Rlinti+RallError
        step with
    | none => none
    | some (Rmax, _) =>
      let VerrorDyn := fm.abstrErrAdaptiveFloat κ A B xs Rmax U redFactor p  -- priv_abstr...
      let trueError := VerrorDyn.interval.normMag                       -- abs(c) + sum(abs(G))
      let perfIndCurr := maximumOver fun i =>                           -- max(trueError./
        if le (trueError i) zero then zero else divUp (trueError i) (errorAdm i)  -- error_adm)
      if ∀ i, le (trueError i) (errorAdm i) = true then some (Rmax, VerrorDyn, trueError)
      else if 2 < perfIndCounter ∧ le perfIndCurr perfIndPrev = false then none  -- diverging
      else fm.step_abstrErrLoopAdaptive κ A B xs Vbase R U options enlarge redFactor p step fuel
        (perfIndCounter + 1) perfIndCurr fun i => mulUp enlarge (trueError i)  -- 1.1*trueError


-- =====================================  MAIN DEFINITION  ====================================== --

/-- One linearization at `options.Δt` from `R`: the inner loop from `errorAdm`, then the step's
sets with the error it accepted, or none if the loop or a linear step fails. -/
def NonlinearSys.FloatHessModel.linReachAdaptivePassFloat (fm : NonlinearSys.FloatHessModel 𝕋 n m)
    (κ : ℕ) (U : Zonotope (Vec 𝕋 m)) (options : LinearSys.ReachFloatOptions 𝕋)
    (enlarge redFactor : 𝕋) (p fuel : ℕ) (R : Zonotope (Vec 𝕋 n)) (errorAdm : Vec 𝕋 n)
    (step : NonlinearSys.LinearStep := .reachFloatInput) :
    Option (NonlinearSys.LinReachAdaptivePass 𝕋 n) := do
  let Δt := options.Δt                                              -- options.timeStep
  let xs := (fm.toFloatModel.linPointFloat Δt R U).1                -- p.x
  let us := U.c                                                     -- p.u
  let A := (fm.toFloatModel.linearizeFloat xs us).1                 -- A
  let B := (fm.toFloatModel.linearizeFloat xs us).2                 -- B
  let f₀ := fm.f (Interval.point xs) (Interval.point us)            -- f0
  let Vbase := f₀.zonotope ⊞                                        -- uTrans ⊕ B(U - p.u)
    Mtimes.mtimes (𝕄 := Mat 𝕋) (ContSet := 𝒵[𝕋]) B (Recenter.recenter U)
  let E ← fm.step_abstrErrLoopAdaptive κ A B xs Vbase R U options enlarge redFactor p step
    fuel 1 zero errorAdm                                            -- the loop
  let S ← NonlinearSys.oneStepFloat A xs (Vbase ⊞ E.2.1) R options step  -- Rti, Rtp with Rerror
  let Rerror := (LinearSys.canonicalFloat A : LinearSys 𝕋 n).errorSolutionAdaptiveFloat Δt
    options.η E.2.1 none                                            -- errorSolution_adaptive
  pure { Rti := S.1, Rtp := S.2, A := A, xs := xs, Rmax := E.1, trueError := E.2.2,
         abstrerr := fun i => sumUp fun j => absolute (Rerror.G j i),  -- sum(abs(G(Rerror)),2)
         Gzero := fun i => le (sumUp fun j => absolute (E.2.1.G j i)) zero }  -- vecnorm(G,1,2)==0

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
