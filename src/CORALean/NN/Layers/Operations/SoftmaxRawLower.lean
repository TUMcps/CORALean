import CORALean.NN.Layers.Operations.SoftmaxDenomUp

/-!
# Softmax's raw lower bound

`(1 + ∑_{j≠i} exp(hi j - lo i))⁻¹` with the denominator overestimated and the reciprocal rounded
down, where `softmaxExpInRange` licenses `expUp`; zero elsewhere.
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

/-- The reciprocal of `softmaxDenomUp` rounded down, or zero where `expUp` is not licensed. -/
def softmaxRawLower (k : ℕ) (I : Interval (Vec 𝕋 n)) (i : Fin n) : 𝕋 :=
  if softmaxExpInRange k I i = true then divDown one (softmaxDenomUp k I i) else zero

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
