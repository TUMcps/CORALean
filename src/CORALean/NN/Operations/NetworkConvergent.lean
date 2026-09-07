import CORALean.NN.Operations.Convergent
import CORALean.NN.RefinableNetwork

/-!
# What it takes for a whole network's refinement to converge

Every layer `Convergent`, and every tail Lipschitz so that a residual left
early is still small at the output: an earlier layer's residual is amplified
by everything downstream, so without a bound on the tail a vanishing residual
at one layer buys nothing at the network's output. The bound is a hypothesis
rather than a weakened claim, and it is one every standard layer meets — a
linear layer by its matrix, an activation by its own slope.
-/

-- Authors:       Tobias Ladner
-- Written:       05-September-2026
-- Last update:   06-September-2026
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- Every layer convergent, and every tail Lipschitz so that a residual left
early is still small at the output. -/
def RefinableNetwork.Convergent : ∀ {n m : ℕ}, RefinableNetwork S n m → Prop
  | _, _, .nil => True
  | _, _, .cons L rest =>
      L.Convergent ∧ (∃ K : NNReal, LipschitzWith K rest.eval) ∧ rest.Convergent

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
