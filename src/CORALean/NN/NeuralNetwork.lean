import CORALean.NN.Layer

/-!
# Neural networks: the computation graph

CORA's `neuralNetwork`: layers applied one after another, the dimensions
chaining so that a network is well-formed by construction and `eval` needs no
side condition.

A chain rather than a node-and-edge graph, and that is not a restriction. A
layer is any function with an enclosure, so a branch is expressed by widening
the vector and carrying the branched coordinates along — `Layer.identity` on
that block, a linear layer to route or to duplicate, and the two paths rejoined
by another. That keeps every value in one set, so the dependency between the
branches survives; splitting into two sets and recombining them would lose it,
which is precisely the precision a skip connection is there to preserve.

`image` is what verification is about and what nothing computes: the exact
image, which `propagate` encloses.
-/

-- Authors:       Tobias Ladner
-- Written:       02-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open ContSet

variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)] {n m k : ℕ}


-- ========================================  MAIN TYPE  ========================================= --

inductive NeuralNetwork (S : ℕ → Type) [∀ n, ContSet (S n) (Vec ℝ n)] : ℕ → ℕ → Type where
  | nil {n : ℕ} : NeuralNetwork S n n
  | cons {n m k : ℕ} (L : Layer S n m) (rest : NeuralNetwork S m k) : NeuralNetwork S n k

def NeuralNetwork.eval : ∀ {n m : ℕ}, NeuralNetwork S n m → Vec ℝ n → Vec ℝ m
  | _, _, .nil, x => x
  | _, _, .cons L rest, x => rest.eval (L.eval x)

/-- The exact image a network produces: not computable, and what `propagate`
encloses. -/
def NeuralNetwork.image (nn : NeuralNetwork S n m) (X : Set (Vec ℝ n)) : Set (Vec ℝ m) :=
  nn.eval '' X

/-- One layer, so that a single layer needs no special case anywhere. -/
def NeuralNetwork.ofLayer (L : Layer S n m) : NeuralNetwork S n m := .cons L .nil

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
