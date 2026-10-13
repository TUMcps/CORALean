import CORALean.ContDynamics.LinearSys.MatExp.Operations.CorrCoeffLowFloat
import CORALean.ContDynamics.LinearSys.MatExp.Operations.TaylorCoeffBoundsFloat
import CORALean.ContSet.Conversion.Float.Zonotope_to_Interval
import CORALean.ContSet.Interval.Float.Operations.Smul
import CORALean.ContSet.Zonotope.Float.Operations.MatPow

/-!
# `MatExp.matZonoCorrTerm`, what order `i` contributes at a float matrix zonotope

`Real.MatExp.matZonoCorrTerm` rounded: the box of the `i`-th matrix-zonotope power
(`Zonotope.matPow`, then `interval`), against the scalar `corrCoeff i · r^i/i!`
replaced by the range `[κ·r^i/i!, 0]` it lies in, exactly as `intervalCorrTerm`
does at a box. CORA boxes the powers before the correction, and so does this.
-/

-- Authors:       Tobias Ladner
-- Written:       09-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `corrCoeff i · r^i/i!` times the box of the `i`-th power, for a nonnegative `r`. -/
def MatExp.matZonoCorrTerm (M : Zonotope (Mat 𝕋 n n)) (r : 𝕋) (i : ℕ) :
    Interval (Mat 𝕋 n n) :=
  let cLo := mulDown (MatExp.corrCoeffLow i) (MatExp.taylorCoeffBounds r i).2  -- κ · r^i/i!
  (Interval.smul cLo zero (M.matPow i).matInterval).materialiseMat               -- [κ r^i/i!, 0] Mᵢ

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
