module

public import CORALean.NN.Layers.Layer

@[expose] public section

/-!
# Neural networks: the computation graph

CORA's `neuralNetwork`: layers applied one after another, the dimensions chaining so that a network
is well-formed by construction. `output` ends the chain, and `layer curr tail` puts one layer of any
`Enclose` kind in front of the rest, the instance travelling with each layer (so `NeuralNetwork` is
in `Type 1`); a network is itself an `Enclose` kind and nests through `Enclose.pack`. A chain rather
than a node-and-edge graph is no restriction: a branch widens the vector and carries the branched
coordinates along. What a network computes is its layers' `eval`s composed; `Encloses`, in
`Definitions/Encloses.lean`, is the weaker, relational statement the reduction results need.

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
