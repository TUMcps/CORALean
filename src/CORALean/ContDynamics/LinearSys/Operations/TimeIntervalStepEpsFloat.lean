module

public import CORALean.ContDynamics.LinearSys.MatExp.Operations.TuneOrderFloat
public import CORALean.ContDynamics.LinearSys.Operations.TimeIntervalFloat

@[expose] public section

/-!
# A float step stated against an admissible error rather than an order

`timeIntervalStepEps` computed in `𝕋`, the order chosen as [1, Alg. 2] lines 4-5 choose it:
the order is the first one `MatExp.tuneOrder` finds
at the float bound `nrm ≥ ‖rA‖` whose float remainder bound is under `ε`, where
`timeIntervalStepEps` names the least such order by `expRemainderOrder`'s infimum. The search
gives up after `fuel` orders, so the result is an `Option`.

## Inputs
* `sys` – linear system
* `r` – float step length
* `ε` – float admissible error
* `fuel` – number of orders tried
* `X₀` – initial float zonotope

## Output
* float time-interval step at the first order under the error, if found

## References

* [1] M. Wetzlinger, N. Kochdumper and M. Althoff. "Adaptive parameter tuning for reachability
      analysis of linear systems". 2020 59th IEEE Conference on Decision and Control (CDC), 2020.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       08-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Float

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `timeIntervalFloat` at the first order whose float remainder bound is under `ε`, or
`none` if none of the `fuel` orders from `2` is. -/
def LinearSys.timeIntervalStepEpsFloat (sys : LinearSys 𝕋 n) (r ε : 𝕋) (fuel : ℕ)
    (X₀ : Zonotope (Vec 𝕋 n)) : Option (Zonotope (Vec 𝕋 n)) := do
  let nrm := MatExp.normUpperBound (Interval.smul r r (Interval.point sys.A))  -- ≥ ‖r A‖
  let η ← MatExp.tuneOrder nrm ε fuel                               -- the order for ε
  pure (sys.timeIntervalFloat r η X₀)                           -- the step at it

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
