import CORALean.NN.RefinableNetwork

/-!
# The Lipschitz hypothesis, asked of a layer instead of a tail

`RefinableNetwork.Convergent` wants a bound on every *tail*, which is a
statement about a composite and so nothing a layer library can hand over. This
is the per-layer form: each node's own `eval` Lipschitz, one existential per
layer, which is what a linear layer's matrix and an activation's slope actually
give.

`Theorems.EvalLipschitz` turns this into the tail bounds, the constants
multiplying along the chain — so a network is checked one layer at a time and
its tails follow.
-/

-- Authors:       Tobias Ladner
-- Written:       06-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open ContSet

variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- Every layer's own map Lipschitz, with no claim about the composite. -/
def RefinableNetwork.LipschitzLayers : ∀ {n m : ℕ}, RefinableNetwork S n m → Prop
  | _, _, .nil => True
  | _, _, .cons L rest => (∃ K : NNReal, LipschitzWith K L.eval) ∧ rest.LipschitzLayers

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
