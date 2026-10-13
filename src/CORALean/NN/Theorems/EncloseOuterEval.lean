import CORALean.NN.Theorems.ImageSubset
import CORALean.NN.Theorems.SoundEval

/-!
# What a network encloses

Its own function, on every input set, with no hypothesis: `sound_eval` read through
`Sound.image_subset`. This is the guarantee a network gives as an `Enclose` kind.
-/

-- Authors:       Claude Opus 5.5
-- Written:       24-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open ContSet

variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)] {n m : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem NeuralNetwork.enclose_outer (nn : NeuralNetwork S n m) (X : S n) :
    nn.eval.out '' construct X ⊆ construct (nn.enclose X) :=
  (NeuralNetwork.sound_eval nn).image_subset X

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
