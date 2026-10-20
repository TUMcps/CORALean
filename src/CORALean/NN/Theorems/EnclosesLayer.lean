module

public import CORALean.NN.Definitions.Encloses

@[expose] public section

/-!
# Soundness at a layer

Composition at `layer`: the constructor read at `f = h ∘ g`.

## Inputs
* `L` – family of layer types
* `curr` – first layer
* `tail` – remaining network
* `g` – map of the first layer
* `h` – map of the remaining network

## Hypotheses
* `hL` – the first layer encloses its map
* `htail` – the remaining network encloses its map

## Conclusion
* the whole network encloses the composition
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
theorem NeuralNetwork.encloses_layer {L : ℕ → ℕ → Type} [Enclose L S] {curr : L n m}
    {tail : NeuralNetwork S m k} {g : Vec ℝ n → Vec ℝ m} {h : Vec ℝ m → Vec ℝ k}
    (hL : (Enclose.toLayer (S := S) curr).Encloses g) (htail : tail.Encloses h) :
    (NeuralNetwork.layer curr tail).Encloses (h ∘ g) :=
  .layer hL htail fun _ => rfl

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
