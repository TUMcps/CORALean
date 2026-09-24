import CORALean.NN.Layers.Operations.DoubleRounding
import CORALean.NN.Layers.Operations.RelaxationOfAffineConj
import CORALean.NN.Layers.Operations.SigmoidRelaxation

/-!
# The tanh relaxation

`sigmoidRelaxation` read through `tanh t = 2 σ(2t) - 1`: `Relaxation.ofAffineConj` at
`ra = rb = 2`, both doublings by self-addition, and `c = -1`, which `neg one` stores exactly.
-/

-- Authors:       Tobias Ladner
-- Written:       03-September-2026
-- Last update:   23-September-2026
-- Last revision: ---


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
