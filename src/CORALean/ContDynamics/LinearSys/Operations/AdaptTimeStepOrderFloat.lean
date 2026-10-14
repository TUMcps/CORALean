module

public import CORALean.ContDynamics.LinearSys.LinearSys
public import CORALean.ContDynamics.LinearSys.MatExp.Operations.IntervalCorrectionMatrixFloat
public import CORALean.ContDynamics.LinearSys.MatExp.Operations.IntervalInputRemainderFloat
public import CORALean.ContSet.Interval.Float.Operations.Point
public import CORALean.ContSet.Zonotope.Float.Instances
public import CORALean.ContSet.Zonotope.Float.Operations.ErrOp
public import CORALean.Global.Float.ToRat

@[expose] public section

/-!
# `Alg. 2` lines 4-5 in floats: the order sweep

[1, Alg. 2]'s `adaptTimeStepOrder` computed in `𝕋`: sweep the order upward from `η` until
one clears `ε_H ≤ ε_H,max` and `ε_P ≤ ε_P,max,i`, at eq. (21)-(22)'s own sets
`e^{At_i} F_x X₀` and `e^{At_i} E Δt U`, `[e^{At_i}]` an interval matrix. The
errors are the sup-norm `errOp`, read into ℚ through `ToRat`. Eq. (21)'s
`F_u c_u` half is absent: the run carries the constant input separately. An
order also has to pass the float side condition the step's enclosures need.

Tuning only: `adaptiveStepFloat` re-checks the step and order it is given, and
`adaptiveStepFloat_outer` holds for any. A NaN read through `ToRat` is `1.5 · 2 ^ 1024`.
A NaN `errOp` fails the budgets, and the float test `le nrm …` is false on a NaN: the sweep goes on.

## References

* [1] M. Wetzlinger, N. Kochdumper and M. Althoff. "Adaptive parameter tuning
      for reachability analysis of linear systems". CDC, 2020, pp. 5145–5152.
-/

-- Authors:       Claude Opus 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Float FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] [ToRat 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- Lines 4-5: the coarsest order from `η` clearing both bounds, with its
`ε_H` and `ε_P`, and `none` where the sweep reaches `Φ_prop,max` without one. -/
def LinearSys.adaptTimeStepOrderFloat (sys : LinearSys 𝕋 n) (eAt : Interval (Mat 𝕋 n n))
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
    else sys.adaptTimeStepOrderFloat eAt X₀ U εHmax εPi Δt (η + 1) k

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
