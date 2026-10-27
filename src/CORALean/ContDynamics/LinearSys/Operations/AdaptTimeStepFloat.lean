module

public import CORALean.ContDynamics.LinearSys.LinearSys
public import CORALean.ContDynamics.LinearSys.MatExp.Operations.IntervalCorrectionMatrixFloat
public import CORALean.ContDynamics.LinearSys.MatExp.Operations.IntervalInputRemainderFloat
public import CORALean.ContSet.Interval.Float.Operations.Point
public import CORALean.ContSet.Zonotope.Float.Instances
public import CORALean.ContSet.Zonotope.Float.Operations.ErrOp
public import CORALean.Global.Float.RatUp
public import CORALean.Global.Float.Interfaces
public import CORALean.Global.Float.SoundFloatArithmetic
public import CORALean.Global.StepOf

@[expose] public section

/-!
# `Alg. 2` in floats: the step size and the truncation order for one step

`adaptTimeStep` computed in `𝕋`: enlarge the previous step by `1/μ`, clip it to what is left of
the horizon, then run `step_adaptTimeStepSearchFloat` and accumulate `ε_P`, eq. (9). The clip is
CORA's `maxTimeStep`, not [1]'s, whose `Alg. 1` can step past `t_f`: `t_f - t_i` is exact in ℚ,
and `ratUp` turns it into a candidate. Nothing rests on the candidate being exact: the run reads
the step it took back through `ToRat`. Tuning only: `adaptiveStepFloat` re-checks the step and
order it is given, and `adaptiveStepFloat_outer` holds for any. A NaN read through `ToRat` is
`1.5 · 2 ^ 1024`; the clip replaces a NaN `Δt` by the horizon.

## Inputs
* `sys` – linear system
* `eAt` – float exponential enclosure
* `X₀` – initial float zonotope
* `U` – input float zonotope
* `εHmax` – maximal homogeneous error
* `εPmax` – maximal particular error
* `εPacc` – accumulated particular error
* `tf` – final time
* `ti` – step start time
* `Δtprev` – previous step length
* `μ` – shrink factor
* `ηmax` – maximal Taylor order
* `fuel` – number of shrinkings

## Output
* step size, order and both errors, if one is found

## References

* [1] [M. Wetzlinger, N. Kochdumper and M. Althoff. "Adaptive parameter tuning for reachability
      analysis of linear systems". 2020 59th IEEE Conference on Decision and Control (CDC),
      2020.](../../../../../references/2020/wetzlinger-cdc-adaptive-tuning.md)
-/

-- Authors:       Claude Opus 5.5
-- Written:       02-October-2026
-- Last update:   14-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Float FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] [ToRat 𝕋] {n : ℕ}


-- ------------------------------------------  STEPS  ------------------------------------------- --

/-- Lines 4-5: the coarsest order from `η` clearing both bounds, with its
`ε_H` and `ε_P`, and `none` where the sweep reaches `Φ_prop,max` without one. -/
@[step_of LinearSys.adaptTimeStepFloat]
def LinearSys.step_adaptTimeStepOrderFloat (sys : LinearSys 𝕋 n) (eAt : Interval (Mat 𝕋 n n))
    (X₀ U : Zonotope (Vec 𝕋 n)) (εHmax εPi : ℚ) (Δt : 𝕋) : ℕ → ℕ → Option (ℕ × ℚ × ℚ)
  | _, 0 => none
  | η, k + 1 =>
    let eA := Mtimes.mtimes (𝕄 := ℐ[𝕋])  -- [e^{At_i}] ·
      (S := 𝒵[𝕋]) eAt
    let nrm := MatExp.normUpperBound (Interval.smul Δt Δt (Interval.point sys.A))  -- ≥ ‖Δt A‖
    let F := MatExp.intervalCorrectionMatrix (Interval.point sys.A) Δt η   -- F_x(Δt, η)
    let E := MatExp.intervalInputRemainder (Interval.point sys.A) Δt η     -- E(Δt, η) Δt
    let εH := ToRat.toRat                                                  -- 10. calc. HR⁺, ε_H
      (eA (Mtimes.mtimes (𝕄 := ℐ[𝕋])
        (S := 𝒵[𝕋]) F X₀)).errOp
    let εP := ToRat.toRat                                                  -- 11. calc. PR⁺, ε_P
      (eA (Mtimes.mtimes (𝕄 := ℐ[𝕋])
        (S := 𝒵[𝕋]) E U)).errOp
    if le nrm (half (nsmulDown (η + 2) one)) && decide (εH ≤ εHmax) && decide (εP ≤ εPi)
    then some (η, εH, εP)                                                  -- 12. both inside
    else sys.step_adaptTimeStepOrderFloat eAt X₀ U εHmax εPi Δt (η + 1) k

/-- Lines 3-12: shrink `Δt_i` by `μ` until some order clears both bounds,
returning the step, the order and its `ε_H` and `ε_P`. -/
@[step_of LinearSys.adaptTimeStepFloat]
def LinearSys.step_adaptTimeStepSearchFloat (sys : LinearSys 𝕋 n) (eAt : Interval (Mat 𝕋 n n))
    (X₀ U : Zonotope (Vec 𝕋 n)) (εHmax εPmax εPacc tf ti : ℚ) (μ : 𝕋) (ηmax : ℕ) :
    𝕋 → ℕ → Option (𝕋 × ℕ × ℚ × ℚ)
  | _, 0 => none
  | Δt, k + 1 =>
    let εPi := (εPmax - εPacc) / (tf - ti) * ToRat.toRat Δt         -- 2./7. eq. (10)
    match sys.step_adaptTimeStepOrderFloat eAt X₀ U εHmax εPi Δt 2 (ηmax - 1) with
    | some (η, εH, εP) => some (Δt, η, εH, εP)
    | none => sys.step_adaptTimeStepSearchFloat eAt X₀ U εHmax εPmax εPacc tf ti μ ηmax
        (mulDown Δt μ) k                                            -- 8. Δt_i ← Δt_i μ


-- =====================================  MAIN DEFINITION  ====================================== --

/-- [1, Alg. 2]: the step size, the truncation order, its `ε_H` and the
accumulated `ε_P` for step `i`, or `none` where `fuel` shrinkings did not suffice. -/
def LinearSys.adaptTimeStepFloat (sys : LinearSys 𝕋 n) (eAt : Interval (Mat 𝕋 n n))
    (X₀ U : Zonotope (Vec 𝕋 n)) (εHmax εPmax εPacc tf ti : ℚ) (Δtprev μ : 𝕋) (ηmax fuel : ℕ) :
    Option (𝕋 × ℕ × ℚ × ℚ) :=
  -- 1. enlarge the previous step
  let Δt := divUp Δtprev μ
  let maxTimeStep : 𝕋 := ratUp (tf - ti)                            -- t_f - t_i, rounded up
  let Δt' := if ToRat.toRat Δt < tf - ti then Δt else maxTimeStep   -- clipped to the horizon
  match sys.step_adaptTimeStepSearchFloat eAt X₀ U εHmax εPmax εPacc tf ti μ ηmax Δt' fuel with
  | none => none
  -- 13. accumulate, eq. (9)
  | some (Δti, ηi, εH, εP) => some (Δti, ηi, εH, εPacc + εP)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
