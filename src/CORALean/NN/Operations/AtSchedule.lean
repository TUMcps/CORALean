import CORALean.NN.NeuralNetwork
import CORALean.NN.Operations.Schedule

/-!
# Reading a schedule against a network

`atSchedule` is the whole interpretation: a refinable network and a schedule
give a `NeuralNetwork`, each layer at its own pattern. Everything the loop has
to prove reduces to a property of *that* network, so `propagateAt`'s soundness
is a corollary of `NeuralNetwork.propagate_outer` rather than a new induction.
-/

-- Authors:       Tobias Ladner
-- Written:       05-September-2026
-- Last update:   06-September-2026
-- Last revision: ---

namespace CORALean.Real

variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]

/-- The network a schedule names: each layer at its own pattern. -/
def RefinableNetwork.atSchedule : ∀ {n m : ℕ}, RefinableNetwork S n m → Schedule →
    NeuralNetwork S n m
  | _, _, .nil, _ => .nil
  | _, _, .cons L rest, sch =>
      .cons (L.atPattern (Schedule.head sch _)) (rest.atSchedule (Schedule.tail sch))

end CORALean.Real
