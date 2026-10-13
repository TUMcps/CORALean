import CORALean.ContDynamics.LinearSys.MatExp.Operations.TaylorCoeffBoundsFloat
import CORALean.ContSet.Interval.Float.Operations.MatPow
import CORALean.ContSet.Interval.Float.Operations.Smul

/-!
# `MatExp.intervalInputTerm`, the input solution's order `i` over a float box

`Aⁱ r^{i+1}/(i+1)!` of [1, Thm. 3.1], at every member of a float interval
matrix: the power as `matPow`, the scalar as `taylorCoeffBounds`, and the two
joined by `smul`. The float counterpart of `LinearSys.inputTerm` at a point
(a point box) and of `LinParamSys.inputTerm` at a set.

## References

* [1] M. Althoff. "Reachability Analysis and its Application to the Safety
      Assessment of Autonomous Cars". PhD thesis, TU München, 2010.
-/

-- Authors:       Claude Opus 5.5
-- Written:       24-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `Aⁱ r^{i+1}/(i+1)!` over the whole box `A`, for a nonnegative `r`. -/
def MatExp.intervalInputTerm (A : Interval (Mat 𝕋 n n)) (r : 𝕋) (i : ℕ) :
    Interval (Mat 𝕋 n n) :=
  let c := MatExp.taylorCoeffBounds r (i + 1)                   -- r^{i+1}/(i+1)! ∈ [c.1, c.2]
  (Interval.smul c.1 c.2 (Interval.matPow A i)).materialiseMat  -- · Aⁱ

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
