module

public import CORALean.ContDynamics.LinearSys.MatExp.Operations.CorrCoeffLowTightFloat
public import CORALean.ContDynamics.LinearSys.MatExp.Operations.TaylorCoeffBoundsFloat
public import CORALean.ContSet.Interval.Float.Operations.MatPow
public import CORALean.ContSet.Interval.Float.Operations.Smul

@[expose] public section

/-!
# `MatExp.intervalCorrTerm`, what order `i` contributes to the correction

`Real.MatExp.intervalCorrTerm`'s scalar `corrCoeff i · r^i/i!` against the box
the `i`-th power lies in, the scalar replaced by the range `[κ·r^i/i!, 0]` it
lies in: `corrCoeff i` is in `[corrCoeffLowTight i, 0]` and `r^i/i!` below
`taylorCoeffBounds`'s upper end.

## Inputs
* `A` – float interval matrix
* `r` – float step length
* `i` – order index

## Output
* float interval matrix of the order's correction term over the box
-/

-- Authors:       Claude Opus 5.5
-- Written:       24-September-2026
-- Last update:   18-November-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `corrCoeff i · r^i/i! · Aⁱ` over the whole box `A`, for a nonnegative `r`. -/
def MatExp.intervalCorrTerm (A : Interval (Mat 𝕋 n n)) (r : 𝕋) (i : ℕ) :
    Interval (Mat 𝕋 n n) :=
  let cLo := mulDown (MatExp.corrCoeffLowTight i) (MatExp.taylorCoeffBounds r i).sup  -- κ · r^i/i!
  (Interval.smul cLo zero (Interval.matPow A i)).materialiseMat  -- [κ r^i/i!, 0] Aⁱ

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
