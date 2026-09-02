import CORALean.NN.NeuralNetwork

/-!
# Propagating a set through the graph

The whole verification pipeline, and it is one line per constructor: hand the
input set to the first layer and the result to the rest. No layer sees anything
but a set of the representation, so nothing here knows which representation that
is or which layers these are.

Precision is entirely the layers' business. A representation that loses nothing
at a linear layer and a great deal at an activation propagates exactly that,
step by step, and this definition is unchanged by it.
-/

-- Authors:       Tobias Ladner
-- Written:       02-September-2026
-- Last update:   ---
-- Last revision: ---

namespace CORALean.Real

open ContSet

variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]

def NeuralNetwork.propagate : ∀ {n m : ℕ}, NeuralNetwork S n m → S n → S m
  | _, _, .nil, s => s
  | _, _, .cons L rest, s => rest.propagate (L.propagate s)

end CORALean.Real
