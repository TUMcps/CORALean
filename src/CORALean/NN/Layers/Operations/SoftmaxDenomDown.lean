module

public import CORALean.ContSet.Interval.Float.Interval
public import CORALean.Global.Float.Exp
public import CORALean.NN.Layers.Operations.Basic

@[expose] public section

/-!
# Softmax's denominator from below

`1 + ∑_{j≠i} exp(x j - x i)` at the box's corner where every ratio is smallest, underestimated
through `expDown`, and held above one by an exact `maximum`, so the quotient that follows never
meets a divisor the arithmetic says nothing about.

## Inputs
* `k` – reduction depth of the exponential
* `I` – box of the layer's input
* `i` – output coordinate

## Output
* lower bound of the denominator, at least one
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

/-- Never below one, so `divUp` never meets an unconstrained divisor. -/
def softmaxDenomDown (k : ℕ) (I : Interval (Vec 𝕋 n)) (i : Fin n) : 𝕋 :=
  maximum one (addDown one
    (sumOffDown i fun j => expDown k (subDown (I.inf j) (I.sup i))))

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
