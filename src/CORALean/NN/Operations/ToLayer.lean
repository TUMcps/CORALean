import CORALean.NN.Theorems.EncloseOuter

/-!
# A network is a layer

Which is what makes a block one: a sub-network fits wherever a layer does, and
`Layer.comp` and `NeuralNetwork.cons` describe the same graph. Nesting costs
nothing and is checked by nobody.

A layer is its `enclose` and nothing else, so this is that field and no proof:
what the block computes is said by `NeuralNetwork.Sound.enclose_outer`, which
is exactly `Layer.Sound` at the same function.
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
