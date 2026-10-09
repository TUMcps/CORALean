import CORALean.ContSet.Interval.Float.Interval
import CORALean.NN.Layers.Operations.ExpUpLimit

/-!
# Where softmax's `expUp` is licensed

Every `exp (hi j - lo i)` with `j ≠ i` has its argument, rounded up, compared with `expUpLimit k`.
The comparison is a run-time test of `expUp`'s hypothesis, so a box too wide for it is told apart
from one that is not.
-/

-- Authors:       Tobias Ladner
-- Written:       08-October-2026
-- Last update:   08-October-2026
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Float Float.FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- Whether `subUp (sup j) (inf i)` is at most `expUpLimit k` for every `j ≠ i`. -/
def softmaxExpInRange (k : ℕ) (I : Interval (Vec 𝕋 n)) (i : Fin n) : Bool :=
  (List.finRange n).all fun j => decide (j = i) || le (subUp (I.sup j) (I.inf i)) (expUpLimit k)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
