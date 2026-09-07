import CORALean.NN.Theorems.EncloseOuter

/-!
# A network is a layer

Which is what makes a block one: a sub-network fits wherever a layer does, and
`Layer.comp` and `NeuralNetwork.cons` describe the same graph. Its enclosure
obligation is already proved, so nesting costs nothing and is checked by nobody.

The definition needs `enclose_outer`, so it sits after the theorem rather than
beside `enclose` — an operation whose result carries a proof can only be
built where the proof is.
-/

-- Authors:       Tobias Ladner
-- Written:       02-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open ContSet

variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)] {n m : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def NeuralNetwork.toLayer (nn : NeuralNetwork S n m) : Layer S n m where
  eval := nn.eval
  enclose := nn.enclose
  enclose_outer := nn.enclose_outer

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
