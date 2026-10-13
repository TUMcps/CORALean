module

public import CORALean.ContDynamics.NonlinearSys.Operations.LinReachFloat

@[expose] public section

/-!
# The float `linReach` loop, at `alg = 'lin'` or `'poly'`

`linReachFloat` iterated `k` times, the set a step reaches at its end being the
set the next one starts from — the while loop of [1, Alg. 1] — collecting each
step's set over its whole interval. One failed step fails the run: a later step
would start from a set nothing has enclosed.

## References

* [1] M. Althoff. "Reachability Analysis of Nonlinear Systems using Conservative
      Polynomialization and Non-Convex Sets". HSCC 2013.
-/

-- Authors:       Claude Opus 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Float

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] [ToRat 𝕋] {n m : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `R(τ_0), …, R(τ_{k-1})` of `k` steps abstracted by `alg` from `R`, or `none` if
one of them fails. -/
def NonlinearSys.FloatHessModel.linReachRunFloat (fm : NonlinearSys.FloatHessModel 𝕋 n m)
    (alg : NonlinearSys.LinReachAlg) (U : Zonotope (Vec 𝕋 m)) (options : LinearSys.ReachOptions 𝕋) :
    ℕ → Zonotope (Vec 𝕋 n) → Option (List (Zonotope (Vec 𝕋 n)))
  | 0, _ => some []
  | k + 1, R => do
    let step ← fm.linReachFloat alg U options R                    -- (R(τ), R(t + Δt))
    let rest ← fm.linReachRunFloat alg U options k step.2          -- the steps after it
    pure (step.1 :: rest)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
