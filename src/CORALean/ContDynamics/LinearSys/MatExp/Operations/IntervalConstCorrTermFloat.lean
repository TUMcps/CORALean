module

public import CORALean.ContDynamics.LinearSys.MatExp.Operations.CorrCoeffLowFloat
public import CORALean.ContDynamics.LinearSys.MatExp.Operations.TaylorCoeffBoundsFloat
public import CORALean.ContSet.Interval.Float.Operations.MatPow
public import CORALean.ContSet.Interval.Float.Operations.Smul

@[expose] public section

/-!
# `MatExp.intervalConstCorrTerm`, what order `i + 2` contributes to the integrated correction

`Real.MatExp.intervalConstCorrTerm`'s scalar `corrCoeff (i+2) · r^{i+2}/(i+2)!` against the
box the `(i+1)`-th power lies in, the scalar replaced by the range `[κ·r^{i+2}/(i+2)!, 0]` it
lies in: `corrCoeff (i+2)` is in `[corrCoeffLow (i+2), 0]` and `r^{i+2}/(i+2)!` is below
`taylorCoeffBounds`'s upper end. The float counterpart of the order [1, Prop. 3.4]'s
`constCorrectionMatrix` sums, one factorial further along and one matrix power back than
`intervalCorrTerm`.

## References

* [1] M. Althoff. "Reachability Analysis and its Application to the Safety
      Assessment of Autonomous Cars". PhD thesis, TU München, 2010.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       08-October-2026
-- Last update:   14-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `corrCoeff (i+2) · r^{i+2}/(i+2)! · A^{i+1}` over the whole box `A`, for a nonnegative
`r`. -/
def MatExp.intervalConstCorrTerm (A : Interval (Mat 𝕋 n n)) (r : 𝕋) (i : ℕ) :
    Interval (Mat 𝕋 n n) :=
  let c := MatExp.taylorCoeffBounds r (i + 2)                          -- r^{i+2}/(i+2)! ≤ c.sup
  let cLo := mulDown (MatExp.corrCoeffLow (i + 2)) c.sup                 -- κ r^{i+2}/(i+2)!
  (Interval.smul cLo zero (Interval.matPow A (i + 1))).materialiseMat  -- [cLo, 0] A^{i+1}

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
