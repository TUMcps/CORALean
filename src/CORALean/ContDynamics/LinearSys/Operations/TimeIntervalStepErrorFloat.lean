module

public import CORALean.ContDynamics.LinearSys.MatExp.Operations.ExpRemainderBoundFloat
public import CORALean.ContDynamics.LinearSys.Operations.ExpNormUpFloat
public import CORALean.ContSet.Zonotope.Float.Operations.AbsBoundError

@[expose] public section

/-!
# How far `timeInterval` reaches past the run, in floats

`timeIntervalStepError`, the `ε_H` of [1, Alg. 2] (eq. (21)) with the hull term, rounded up
in `𝕋`: `Σⱼ|X₀|ⱼ (‖e^{rA} - I‖ + 2(e^x - 1 - x + E(rA, η)))` at `x = r‖A‖`. The hull term
`‖e^{rA} - I‖` is bounded by `e^{‖rA‖} - 1` (`norm_exp_sub_one_le_exp_norm`), so no matrix
exponential is taken; the other factors are as in `timeIntervalStepCurvatureErrorFloat`.

## Inputs
* `sys` – linear system
* `r` – float step length
* `η` – Taylor order
* `X₀` – initial float zonotope

## Output
* float upper bound of how far the time-interval step reaches past the run

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

/-- `Σⱼ|X₀|ⱼ (‖e^{rA} - I‖ + 2(e^{r‖A‖} - 1 - r‖A‖ + E(rA, η)))`, rounded up. -/
def LinearSys.timeIntervalStepErrorFloat (sys : LinearSys 𝕋 n) (r : 𝕋) (η : ℕ)
    (X₀ : Zonotope (Vec 𝕋 n)) : 𝕋 :=
  let S := sumUp fun j => X₀.absBoundError j                              -- ≥ Σⱼ |X₀|ⱼ
  let nrm := MatExp.normUpperBound (Interval.smul r r (Interval.point sys.A))  -- ≥ r ‖A‖
  let hull := subUp (sys.expNormUpFloat r η) one                         -- ≥ ‖e^{rA} - I‖
  let quad := subUp hull nrm                                             -- ≥ e^{r‖A‖} - 1 - r‖A‖
  let rem := MatExp.expRemainderBound nrm η                              -- ≥ E(rA, η)
  mulUp S (addUp hull (addUp (addUp quad rem) (addUp quad rem)))         -- S (hull + 2(…))

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
