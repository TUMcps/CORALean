import CORALean.ContDynamics.LinearSys.LinearSys
import CORALean.ContDynamics.LinearSys.MatExp.Operations.IntervalInputTermFloat
import CORALean.ContSet.Interval.Float.Operations.Point
import CORALean.ContSet.Zonotope.Float.Instances

/-!
# The exact orders of the input solution, summed in floats

`inputTaylorSum` computed in `𝕋`: order `i` is `MatExp.intervalInputTerm`, the
float box holding `Aⁱ r^{i+1}/(i+1)!` at the stored `A`, applied to the input
set by `Zonotope.mtimesIntervalMat`, and the orders summed by `plus` one at a
time, exactly as the real sum is.
-/

-- Authors:       Tobias Ladner
-- Written:       01-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Float

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `⊕_{i ≤ η} [Aⁱ r^{i+1}/(i+1)!] V`, at index `η`. -/
def LinearSys.inputTaylorSumFloat (sys : LinearSys 𝕋 n) (r : 𝕋) (V : Zonotope (Vec 𝕋 n)) :
    ℕ → Zonotope (Vec 𝕋 n)
  | 0 => Mtimes.mtimes (𝕄 := fun m n => Interval (Mat 𝕋 m n)) (S := fun k => Zonotope (Vec 𝕋 k))
      (MatExp.intervalInputTerm (Interval.point sys.A) r 0) V
  | i + 1 => sys.inputTaylorSumFloat r V i ⊞ Mtimes.mtimes (𝕄 := fun m n => Interval (Mat 𝕋 m n))
    (S := fun k => Zonotope (Vec 𝕋 k))
      (MatExp.intervalInputTerm (Interval.point sys.A) r (i + 1)) V

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
