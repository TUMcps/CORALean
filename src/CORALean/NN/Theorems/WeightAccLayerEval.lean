import CORALean.NN.Operations.WeightAccLayer
import CORALean.NN.Operations.WeightAccEval
import CORALean.NN.Operations.WeightLayerEval

/-!
# The flushed layer computes the accumulated map
-/

-- Authors:       Tobias Ladner
-- Written:       03-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix

variable {α : Type} [Semiring α] {n m k d : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- `acc.layer` and `acc` have the same map. -/
theorem WeightAcc.layer_eval (acc : WeightAcc α n d) (x : Fin n → α) :
    acc.layer.eval x = acc.eval x := by
  cases acc <;> rfl

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
