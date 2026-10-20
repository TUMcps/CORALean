module

public import CORALean.NN.Layers.Operations.DoubleRounding
public import CORALean.NN.Layers.Operations.RelaxationOfAffineConj
public import CORALean.NN.Layers.Operations.SigmoidRelaxation

@[expose] public section

/-!
# The tanh relaxation

`sigmoidRelaxation` read through `tanh t = 2 σ(2t) - 1`: `Relaxation.ofAffineConj` at
`ra = rb = 2`, both doublings by self-addition, and `c = -1`, which `neg one` stores exactly.

## Inputs
* `k` – reduction depth of the exponential

## Output
* tanh relaxation through the sigmoid relaxation
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-September-2026
-- Last update:   23-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Float Float.FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `sigmoidRelaxation` read through `tanh_eq_sigmoid`: `a = b = 2`, `c = -1`. -/
def tanhRelaxation (k : ℕ) : Relaxation 𝕋 :=
  Relaxation.ofAffineConj (sigmoidRelaxation k) doubleRounding doubleRounding (neg one)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
