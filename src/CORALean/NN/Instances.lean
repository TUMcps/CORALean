import CORALean.NN.Theorems.EncloseOuterEval

/-!
# A network is a layer kind

`NeuralNetwork S` is itself an `Enclose` kind, which is why `Enclose` is universe-polymorphic:
a network stores its layers' kinds and lives in `Type 1`. A network, or a block of one, goes
into another as one layer through `Enclose.pack`.
-/

-- Authors:       Claude Opus 5.5
-- Written:       24-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]


-- ========================================  INSTANCES  ========================================= --

instance : Enclose (NeuralNetwork S) S where
  eval := NeuralNetwork.eval
  enclose := NeuralNetwork.enclose
  enclose_outer := NeuralNetwork.enclose_outer

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
