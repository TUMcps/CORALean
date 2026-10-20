module

public import CORALean.NN.Layers.Operations.SoftmaxDenomDown

@[expose] public section

/-!
# Softmax's raw upper bound

An underestimated denominator, so the quotient is an overestimate — the one direction
available without a hypothesis on the exponential's argument.

## Inputs
* `k` – reduction depth of the exponential
* `I` – box of the layer's input
* `i` – output coordinate

## Output
* raw upper bound of the coordinate's softmax
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

/-- An underestimated denominator, so the quotient is an overestimate. -/
def softmaxRawUpper (k : ℕ) (I : Interval (Vec 𝕋 n)) (i : Fin n) : 𝕋 :=
  divUp one (softmaxDenomDown k I i)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
