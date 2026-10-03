import CORALean.NN.Definitions.WeightNetwork
import CORALean.NN.Operations.WeightLayerEval

/-!
# What a weight network computes
-/

-- Authors:       Tobias Ladner
-- Written:       03-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix

variable {α : Type} [Semiring α] {n m k d : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The composite of the layers' maps, first layer first. -/
def WeightNetwork.eval : ∀ {n m : ℕ}, WeightNetwork α n m → (Fin n → α) → (Fin m → α)
  | _, _, .nil, x => x
  | _, _, .cons L rest, x => rest.eval (L.eval x)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
