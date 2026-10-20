module

public import CORALean.NN.Definitions.Encloses

@[expose] public section

/-!
# Soundness is stable under agreeing functions

What lets a caller name the composite in its own terms.

## Inputs
* `nn` – network
* `f` – map the network encloses
* `f'` – map agreeing with it

## Hypotheses
* `h` – the network encloses the first map
* `hff` – the two maps agree everywhere

## Conclusion
* the network encloses the second map
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

/-- Soundness is stable under replacing the function by one that agrees with it
everywhere, which is what lets a caller name the composite in its own terms. -/
theorem NeuralNetwork.Encloses.congr {nn : NeuralNetwork S n m} {f f' : Vec ℝ n → Vec ℝ m}
    (h : nn.Encloses f) (hff : ∀ x, f' x = f x) : nn.Encloses f' := by
  induction h with
  | output hf => exact .output fun x => by rw [hff x, hf x]
  | layer hL htail hf _ => exact .layer hL htail fun x => by rw [hff x, hf x]

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
