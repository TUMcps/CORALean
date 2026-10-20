module

public import CORALean.NN.Layers.Operations.SoftmaxRawLower
public import CORALean.NN.Layers.Operations.SoftmaxRawUpper
public import CORALean.NN.Layers.Operations.SumOffUp

@[expose] public section

/-!
# Softmax's box

The lower bound is the larger of the normalization — `y i ≥ 1 - ∑_{j≠i} ru j`, which needs only
upper bounds and so only `expDown` — and the raw lower bound, which needs `expUp` and so is
computed only where `aux_softmaxExpInRange` licenses it, and is zero elsewhere. The upper is the raw
bound capped at one, the `1` being what the same identity gives at a raw lower bound of zero.

## Inputs
* `k` – reduction depth of the exponential
* `I` – box of the layer's input

## Output
* box enclosing the softmax of every point of the input box
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-September-2026
-- Last update:   23-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Float Float.FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The larger of the raw bound and the normalization below, the raw bound capped at one above. -/
def softmaxBox (k : ℕ) (I : Interval (Vec 𝕋 n)) : Interval (Vec 𝕋 n) where
  inf := fun i =>
    maximum (softmaxRawLower k I i)
      (maximum zero (subDown one (sumOffUp i fun j => softmaxRawUpper k I j)))
  sup := fun i => minimum (softmaxRawUpper k I i) one

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
