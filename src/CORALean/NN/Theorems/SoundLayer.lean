module

public import CORALean.NN.Definitions.Sound

@[expose] public section

/-!
# Soundness at a layer

Composition at `layer`: the constructor read at `f = h ∘ g`.
-/

-- Authors:       Claude Opus 5
-- Written:       02-September-2026
-- Last update:   24-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open ContSet

variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)] {n m k : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- Composition at `layer`, which is the constructor read at `f = h ∘ g`. -/
theorem NeuralNetwork.sound_layer {L : ℕ → ℕ → Type} [Enclose L S] {curr : L n m}
    {tail : NeuralNetwork S m k} {g : Vec ℝ n → Vec ℝ m} {h : Vec ℝ m → Vec ℝ k}
    (hL : (Enclose.toLayer (S := S) curr).Sound g) (htail : tail.Sound h) :
    (NeuralNetwork.layer curr tail).Sound (h ∘ g) :=
  .layer hL htail fun _ => rfl

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
