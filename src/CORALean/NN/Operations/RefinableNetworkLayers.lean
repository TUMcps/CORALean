import CORALean.NN.Definitions.RefinableNetwork

/-!
# The layers of a refinable network

The layers in order, each with its dimensions: CORA's `obj.layers`.
-/

-- Authors:       Tobias Ladner
-- Written:       03-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open ContSet

variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The layers, first layer first, each tagged with its input and output width. -/
def RefinableNetwork.layers : ∀ {n m : ℕ}, RefinableNetwork S n m →
    List (Σ a b : ℕ, RefinableLayer S a b)
  | _, _, .nil => []
  | _, _, .cons L rest => ⟨_, _, L⟩ :: rest.layers

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
