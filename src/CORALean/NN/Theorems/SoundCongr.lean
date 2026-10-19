module

public import CORALean.NN.Definitions.Sound

@[expose] public section

/-!
# Soundness is stable under agreeing functions

What lets a caller name the composite in its own terms.
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
theorem NeuralNetwork.Sound.congr {nn : NeuralNetwork S n m} {f f' : Vec ℝ n → Vec ℝ m}
    (h : nn.Sound f) (hff : ∀ x, f' x = f x) : nn.Sound f' := by
  induction h with
  | output hf => exact .output fun x => by rw [hff x, hf x]
  | layer hL htail hf _ => exact .layer hL htail fun x => by rw [hff x, hf x]

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
