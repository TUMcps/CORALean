import CORALean.ContDynamics.LinearSys.MatExp.Operations.ExpRemainderBoundFloat
import CORALean.ContDynamics.LinearSys.Operations.ExpNormUpFloat
import CORALean.ContSet.Zonotope.Float.Operations.AbsBoundError

/-!
# How far `timePointStep` reaches past the run, in floats

`timePointStepError`, the `ε_P` of [1, Alg. 2] (eq. (22)) with the dependency term, rounded
up in `𝕋`: `2 Σⱼ|U|ⱼ r ((e^x - 1) + E(rA, η))` at `x = r‖A‖`, every factor replaced by a
float upper bound as in `timeIntervalStepCurvatureErrorFloat`; `r ≥ 0` is the float step.

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

open CORALean.Float FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `2 Σⱼ|U|ⱼ r ((e^{r‖A‖} - 1) + E(rA, η))`, rounded up. -/
def LinearSys.timePointStepErrorFloat (sys : LinearSys 𝕋 n) (r : 𝕋) (η : ℕ)
    (U : Zonotope (Vec 𝕋 n)) : 𝕋 :=
  let S := sumUp fun j => U.absBoundError j                               -- ≥ Σⱼ |U|ⱼ
  let nrm := MatExp.normUpperBound (Interval.smul r r (Interval.point sys.A))  -- ≥ r ‖A‖
  let lin := subUp (sys.expNormUpFloat r η) one                          -- ≥ e^{r‖A‖} - 1
  let rem := MatExp.expRemainderBound nrm η                              -- ≥ E(rA, η)
  mulUp (mulUp (addUp S S) r) (addUp lin rem)                            -- 2 S r (… + …)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
