import CORALean.ContDynamics.LinearSys.MatExp.Operations.CorrCoeffLowFloat
import CORALean.ContDynamics.LinearSys.MatExp.Operations.TaylorCoeffBoundsFloat
import CORALean.ContSet.Interval.Float.Operations.MatPow
import CORALean.ContSet.Interval.Float.Operations.Smul

/-!
# `MatExp.intervalCorrTerm`, what order `i` contributes to the correction

`Real.MatExp.intervalCorrTerm`'s scalar `corrCoeff i · r^i/i!` against the box
the `i`-th power lies in, the scalar replaced by the range `[κ·r^i/i!, 0]` it
lies in: `corrCoeff i` is in `[corrCoeffLow i, 0]` and `r^i/i!` below
`taylorCoeffBounds`'s upper end.
-/

-- Authors:       Claude Opus 5.5
-- Written:       24-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `corrCoeff i · r^i/i! · Aⁱ` over the whole box `A`, for a nonnegative `r`. -/
def MatExp.intervalCorrTerm (A : Interval (Mat 𝕋 n n)) (r : 𝕋) (i : ℕ) :
    Interval (Mat 𝕋 n n) :=
  let cLo := mulDown (MatExp.corrCoeffLow i) (MatExp.taylorCoeffBounds r i).2  -- κ · r^i/i!
  (Interval.smul cLo zero (Interval.matPow A i)).materialiseMat               -- [κ r^i/i!, 0] Aⁱ

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
