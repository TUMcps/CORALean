module

public import CORALean.ContDynamics.LinearSys.MatExp.Operations.ExpRemainderBoundFloat
public import CORALean.ContDynamics.LinearSys.Operations.ExpNormUpFloat
public import CORALean.ContSet.Zonotope.Float.Operations.AbsBoundError

@[expose] public section

/-!
# `ε_H`'s widening term alone, in floats

`timeIntervalStepCurvatureError`, the `ε_H` of [1, Alg. 2] (eq. (21)), rounded up in `𝕋`:
`2 Σⱼ|X₀|ⱼ (e^x - 1 - x + E(rA, η))` at `x = r‖A‖`, every factor replaced by a float upper
bound — `absBoundError` for the coordinate reaches, which covers the error box as well,
`nrm ≥ ‖rA‖` for `x`, and `expNormUpFloat` for `e^x`. The factor `2` is `addUp S S`.

## Inputs
* `sys` – linear system
* `r` – float step length
* `η` – Taylor order
* `X₀` – initial float zonotope

## Output
* float upper bound of the correction matrix's widening term

## References

* [1] [M. Wetzlinger, N. Kochdumper and M. Althoff. "Adaptive parameter tuning for reachability
      analysis of linear systems". 2020 59th IEEE Conference on Decision and Control (CDC),
      2020.](../../../../../references/2020/wetzlinger-cdc-adaptive-tuning.md)
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       08-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Float FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `2 Σⱼ|X₀|ⱼ (e^{r‖A‖} - 1 - r‖A‖ + E(rA, η))`, rounded up. -/
def LinearSys.timeIntervalStepCurvatureErrorFloat (sys : LinearSys 𝕋 n) (r : 𝕋) (η : ℕ)
    (X₀ : Zonotope (Vec 𝕋 n)) : 𝕋 :=
  let S := sumUp fun j => X₀.absBoundError j                              -- ≥ Σⱼ |X₀|ⱼ
  let nrm := MatExp.normUpperBound (Interval.smul r r (Interval.point sys.A))  -- ≥ r ‖A‖
  let quad := subUp (subUp (sys.expNormUpFloat r η) one) nrm             -- ≥ e^{r‖A‖} - 1 - r‖A‖
  let rem := MatExp.expRemainderBound nrm η                              -- ≥ E(rA, η)
  mulUp (addUp S S) (addUp quad rem)                                     -- 2 S (… + …)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
