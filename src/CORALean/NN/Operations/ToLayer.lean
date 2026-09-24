import CORALean.NN.Theorems.EncloseOuter

/-!
# A network is a layer

The network's `enclose` as a plain `Layer`, for a statement that wants one: a layer is its
`enclose` and nothing else, so this is that field and no proof, and what the block computes is
said by `NeuralNetwork.Sound.enclose_outer`, exactly `Layer.Sound` at the same function. To
put a network inside another, it is an `Enclose` kind and goes in through `Enclose.pack`.
-/

-- Authors:       Tobias Ladner
-- Written:       02-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open ContSet

variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)] {n m : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def NeuralNetwork.toLayer (nn : NeuralNetwork S n m) : Layer S n m where
  enclose := nn.enclose

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
