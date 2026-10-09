import CORALean.ContDynamics.LinearSys.MatExp.Operations.TuneOrderFloat
import CORALean.ContDynamics.LinearSys.Operations.TimeIntervalStepFloat

/-!
# A float step stated against an admissible error rather than an order

`timeIntervalStepEps` computed in `𝕋`, the order chosen as [1, Alg. 2] lines 4-5 choose it:
the order is the first one `MatExp.tuneOrder` finds
at the float bound `nrm ≥ ‖rA‖` whose float remainder bound is under `ε`, where
`timeIntervalStepEps` names the least such order by `expRemainderOrder`'s infimum. The search
gives up after `fuel` orders, so the result is an `Option`.

## References

* [1] M. Wetzlinger, N. Kochdumper and M. Althoff. "Adaptive parameter tuning
      for reachability analysis of linear systems". CDC, 2020, pp. 5145–5152.
-/

-- Authors:       Tobias Ladner
-- Written:       08-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Float

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `timeIntervalStepFloat` at the first order whose float remainder bound is under `ε`, or
`none` if none of the `fuel` orders from `2` is. -/
def LinearSys.timeIntervalStepEpsFloat (sys : LinearSys 𝕋 n) (r ε : 𝕋) (fuel : ℕ)
    (X₀ : Zonotope 𝕋 n) : Option (Zonotope 𝕋 n) := do
  let nrm := MatExp.normUpperBound (Interval.smul r r (Interval.point sys.A))  -- ≥ ‖r A‖
  let η ← MatExp.tuneOrder nrm ε fuel                               -- the order for ε
  pure (sys.timeIntervalStepFloat r η X₀)                           -- the step at it

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
