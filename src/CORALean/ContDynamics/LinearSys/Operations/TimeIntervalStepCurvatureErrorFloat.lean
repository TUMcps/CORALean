import CORALean.ContDynamics.LinearSys.MatExp.Operations.ExpRemainderBoundFloat
import CORALean.ContDynamics.LinearSys.Operations.ExpNormUpFloat
import CORALean.ContSet.Zonotope.Float.Operations.AbsBoundError

/-!
# `ε_H`'s widening term alone, in floats

`timeIntervalStepCurvatureError`, the `ε_H` of [1, Alg. 2] (eq. (21)), rounded up in `𝕋`:
`2 Σⱼ|X₀|ⱼ (e^x - 1 - x + E(rA, η))` at `x = r‖A‖`, every factor replaced by a float upper
bound — `absBoundError` for the coordinate reaches, which covers the error box as well,
`nrm ≥ ‖rA‖` for `x`, and `expNormUpFloat` for `e^x`. The factor `2` is `addUp S S`.

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

/-- `2 Σⱼ|X₀|ⱼ (e^{r‖A‖} - 1 - r‖A‖ + E(rA, η))`, rounded up. -/
def LinearSys.timeIntervalStepCurvatureErrorFloat (sys : LinearSys 𝕋 n) (r : 𝕋) (η : ℕ)
    (X₀ : Zonotope 𝕋 n) : 𝕋 :=
  let S := sumUp fun j => X₀.absBoundError j                              -- ≥ Σⱼ |X₀|ⱼ
  let nrm := MatExp.normUpperBound (Interval.smul r r (Interval.point sys.A))  -- ≥ r ‖A‖
  let quad := subUp (subUp (sys.expNormUpFloat r η) one) nrm             -- ≥ e^{r‖A‖} - 1 - r‖A‖
  let rem := MatExp.expRemainderBound nrm η                              -- ≥ E(rA, η)
  mulUp (addUp S S) (addUp quad rem)                                     -- 2 S (… + …)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
