module

public import CORALean.ContDynamics.NonlinearSys.Operations.LinReachAdaptiveFloat

@[expose] public section

/-!
# CORA's `reach_adaptive` at `'lin'`, repaired, in floats

The main loop of `@nonlinearSys/reach_adaptive.m` at `alg = 'lin-adaptive'`: while more than
`1e-12` of the time horizon remains and the analysis is not aborted, one step
(`linReachAdaptiveFloat`), whose time-interval set is reduced by `reduce(…, 'adaptive',
5·redFactor)` and time-point set by `reduce(…, 'adaptive', redFactor)`; the latter starts the next
step. `aux_checkForAbortion` stops the loop once the remaining time exceeds `1e9` times the sum of
the last ten step sizes. `k` bounds the number of steps, and the time is kept exactly.

## Inputs
* `fm` – float Hessian model
* `U` – input zonotope
* `o` – adaptive options

## Output
* the states after each step, or none
-/

-- Authors:       Claude Opus 5.5
-- Written:       10-November-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Float FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] [ToRat 𝕋] {n m : ℕ}


-- ------------------------------------------  STEPS  ------------------------------------------- --

/-- `aux_checkForAbortion`: the remaining time over the sum of the last ten step sizes exceeds
`abortRatio`. -/
@[step_of NonlinearSys.FloatHessModel.reachAdaptiveFloat]
def step_abortAdaptive (o : NonlinearSys.LinReachAdaptiveOptions 𝕋) (t : ℚ) (steps : List 𝕋) :
    Bool :=
  let lastNsteps := ((steps.take 10).map ToRat.toRat).sum           -- sum(tVec(end-N+1:end))
  steps ≠ [] && decide (ToRat.toRat o.abortRatio * lastNsteps < o.tFinal - t)


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The states after at most `k` steps of CORA's `reach_adaptive` from `s`, each with its sets
reduced, or none if a step fails. -/
def NonlinearSys.FloatHessModel.reachAdaptiveFloat (fm : NonlinearSys.FloatHessModel 𝕋 n m)
    (U : Zonotope (Vec 𝕋 m)) (o : NonlinearSys.LinReachAdaptiveOptions 𝕋) :
    ℕ → NonlinearSys.LinReachAdaptiveState 𝕋 n →
      Option (List (NonlinearSys.LinReachAdaptiveState 𝕋 n))
  | 0, _ => some []
  | k + 1, s =>
    if ToRat.toRat o.endTol < o.tFinal - s.t ∧ step_abortAdaptive o s.t s.steps = false
    then do                                                         -- MAIN LOOP
      let s' ← fm.linReachAdaptiveFloat U o s                       -- linReach_adaptive
      let s'' := { s' with                                          -- reduction for next step
        R := s'.R.reduceAdaptive o.redFactor o.prec,
        Rτ := s'.Rτ.reduceAdaptive (mulUp o.redFactor (nsmulUp 5 one)) o.prec }
      let rest ← fm.reachAdaptiveFloat U o k s''
      pure (s'' :: rest)
    else some []

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
