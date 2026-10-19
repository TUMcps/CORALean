module

public import CORALean.NN.Theorems.EncloseOuter

@[expose] public section

/-!
# A network is a layer

The network's `enclose` as a plain `Layer`, for a statement that wants one: a layer is its
`enclose` and nothing else, so this is that field and no proof, and what the block computes is
said by `NeuralNetwork.Encloses.enclose_outer`, exactly `Layer.Encloses` at the same function. To
put a network inside another, it is an `Enclose` kind and goes in through `Enclose.pack`.
-/

-- Authors:       Claude Opus 5
-- Written:       02-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open ContSet

variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)] {n m : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def NeuralNetwork.toLayer (nn : NeuralNetwork S n m) : Layer S n m where
  enclose := nn.enclose

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
