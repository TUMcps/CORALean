import CORALean.ContSet.Interval.Float.Interval
import CORALean.Global.Float.Exp
import CORALean.NN.Layers.Operations.SumOffDown

/-!
# Softmax's denominator from below

`1 + ∑_{j≠i} exp(x j - x i)` at the box's corner where every ratio is smallest, underestimated
through `expDown`, and held above one by an exact `maximum`, so the quotient that follows never
meets a divisor the arithmetic says nothing about.
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

/-- Never below one, so `divUp` never meets an unconstrained divisor. -/
def softmaxDenomDown (k : ℕ) (I : Interval 𝕋 n) (i : Fin n) : 𝕋 :=
  maximum one (addDown one
    (sumOffDown i fun j => expDown k (subDown (I.inf j) (I.sup i))))

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
