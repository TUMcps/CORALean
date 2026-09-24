import CORALean.NN.Layers.Operations.SoftmaxRawUpper
import CORALean.NN.Layers.Operations.SumOffUp

/-!
# Softmax's box

The lower bound is the normalization and nothing else — `y i ≥ 1 - ∑_{j≠i} ru j`, which needs
only upper bounds and so only `expDown` — and the upper the raw bound capped at one, the `1`
being what the same identity gives at a raw lower bound of zero. The constraint the standard
treatment throws away is therefore the only lower bound this layer has.
-/

-- Authors:       Tobias Ladner
-- Written:       03-September-2026
-- Last update:   23-September-2026
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Float Float.FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The normalization below, the raw bound capped at one above. -/
def softmaxBox (k : ℕ) (I : Interval 𝕋 n) : Interval 𝕋 n where
  inf := fun i =>
    maximum zero (subDown one (sumOffUp i fun j => softmaxRawUpper k I j))
  sup := fun i => minimum (softmaxRawUpper k I i) one

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
