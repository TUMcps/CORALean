import CORALean.NN.Layers.Operations.SoftmaxExpInRange
import CORALean.NN.Layers.Operations.SumOffUp

/-!
# Softmax's denominator from above

`1 + ∑_{j≠i} exp(hi j - lo i)` at the box's opposite corner, overestimated through `expUp`. Only
meaningful where `softmaxExpInRange` holds.
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

/-- Every term and both additions rounded up. -/
def softmaxDenomUp (k : ℕ) (I : Interval (Vec 𝕋 n)) (i : Fin n) : 𝕋 :=
  addUp one (sumOffUp i fun j => expUp k (subUp (I.sup j) (I.inf i)))

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
