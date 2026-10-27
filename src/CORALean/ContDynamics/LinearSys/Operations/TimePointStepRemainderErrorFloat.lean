module

public import CORALean.ContDynamics.LinearSys.MatExp.Operations.ExpRemainderBoundFloat
public import CORALean.ContDynamics.LinearSys.LinearSys
public import CORALean.ContDynamics.LinearSys.MatExp.Operations.NormUpperBoundFloat
public import CORALean.ContSet.Interval.Float.Operations.Point
public import CORALean.ContSet.Interval.Float.Operations.Smul
public import CORALean.ContSet.Zonotope.Float.Operations.AbsBoundError

@[expose] public section

/-!
# `ε_P`'s widening term alone, in floats

`timePointStepRemainderError`, the `ε_P` of [1, Alg. 2] (eq. (22)), rounded up in `𝕋`:
`2 Σⱼ|U|ⱼ (r E(rA, η))`, the coordinate reaches by `absBoundError` and the remainder by the
float `MatExp.expRemainderBound` at `nrm ≥ ‖rA‖`.

## Inputs
* `sys` – linear system
* `r` – float step length
* `η` – Taylor order
* `U` – input float zonotope

## Output
* float upper bound of the remainder widening term

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

/-- `2 Σⱼ|U|ⱼ (r E(rA, η))`, rounded up. -/
def LinearSys.timePointStepRemainderErrorFloat (sys : LinearSys 𝕋 n) (r : 𝕋) (η : ℕ)
    (U : Zonotope (Vec 𝕋 n)) : 𝕋 :=
  let S := sumUp fun j => U.absBoundError j                               -- ≥ Σⱼ |U|ⱼ
  let nrm := MatExp.normUpperBound (Interval.smul r r (Interval.point sys.A))  -- ≥ r ‖A‖
  let rem := MatExp.expRemainderBound nrm η                              -- ≥ E(rA, η)
  mulUp (addUp S S) (mulUp r rem)                                        -- 2 S (r E)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
