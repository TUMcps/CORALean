module

public import CORALean.ContDynamics.LinearSys.LinearSys
public import CORALean.ContDynamics.LinearSys.MatExp.Operations.NormUpperBoundFloat
public import CORALean.ContSet.Interval.Float.Operations.Point
public import CORALean.ContSet.Interval.Float.Operations.Smul

@[expose] public section

/-!
# How often the step's matrix is halved before its exponential is taken

The tight `[e^{AΔt}]` of `oneStepClosedFormFloat` is `LinearSys.expSquaringFloat`: the Taylor
enclosure at `AΔt / 2^s`, squared `s` times. The scaled matrix is to have a norm of at most `1/2`,
where the series converges at once and its remainder bound is tight, so `s` is the first count
for which the float norm bound of `[Δt/2^s] · A` is at most `1/2`; halving a float is exact.
There is none below `128` only if `‖AΔt‖` is beyond any float.

## Inputs
* `sys` – linear system
* `Δt` – float step length

## Output
* the first count of halvings that brings the norm of the scaled matrix to at most `1/2`, none if
  there is no such count below `128`
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       11-November-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Float FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The first `s < 128` with `‖Δt A‖ / 2^s ≤ 1/2`, the norm taken as `normUpperBound` takes it. -/
def LinearSys.halvingsFloat (sys : LinearSys 𝕋 n) (Δt : 𝕋) : Option ℕ :=
  (List.range 128).find? fun s =>
    le (MatExp.normUpperBound                                     -- ≥ ‖Δt A‖ / 2^s
      (Interval.smul (half^[s] Δt) (half^[s] Δt) (Interval.point sys.A))) (half one)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
