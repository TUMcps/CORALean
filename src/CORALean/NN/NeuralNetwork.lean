module

public import CORALean.NN.Layers.Layer

@[expose] public section

/-!
# Neural networks: the computation graph

CORA's `neuralNetwork`: layers applied one after another, first layer first, the dimensions
chaining so that a network is well-formed by construction. `output` ends the chain, and
`layer curr tail` puts one layer of any `Enclose` kind in front of the rest: the kinds mix
freely, the instance travelling with each layer. Storing the kind puts `NeuralNetwork` in
`Type 1`; a network is itself an `Enclose` kind, and nests into another through
`Enclose.pack`, which forgets the kind in `Type`.

A chain rather than a node-and-edge graph, and that is not a restriction: a branch widens the
vector and carries the branched coordinates along — `IdentityLayer` on that block, a linear
layer to route or duplicate — so every value stays in one set and the dependency survives.

What a network computes is its layers' `eval`s composed, `NeuralNetwork.eval`. `Sound`, in
`Definitions/Sound.lean`, is the weaker, relational statement the reduction and refinement
results need.
-/

-- Authors:       Claude Opus 5
-- Written:       02-September-2026
-- Last update:   24-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open ContSet


-- ========================================  MAIN TYPE  ========================================= --

inductive NeuralNetwork (S : ℕ → Type) [∀ n, ContSet (S n) (Vec ℝ n)] : ℕ → ℕ → Type 1 where
  | output {n : ℕ} : NeuralNetwork S n n
  | layer {n m k : ℕ} {L : ℕ → ℕ → Type} [inst : Enclose L S] (curr : L n m)
      (tail : NeuralNetwork S m k) : NeuralNetwork S n k

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
