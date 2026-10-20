module

public import CORALean.NN.Theorems.DisjointMisclassifiedOfBounds
public import CORALean.NN.Operations.MarginDir
public import CORALean.NN.Definitions.Misclassified
public import CORALean.NN.Theorems.HoldsOfEnclose

@[expose] public section

/-!
# Robust classification, as a specification the outputs avoid

The requirement a classifier is normally verified against: over a whole input
set — an image and everything within a perturbation of it — the same label wins.
Written as an unsafe set, since what must not happen is that some other label
catches up, and then it is checked by the same theorem everything else is.

## Inputs
* `nn` – network
* `f` – map the network encloses
* `X` – input set
* `l` – target label

## Hypotheses
* `hf` – the network encloses the map
* `u` – support bound of the enclosed set for each rival
* `h` – every rival's bound is negative

## Conclusion
* the outputs on the input set avoid the misclassified set
-/

-- Authors:       Claude Opus 5
-- Written:       02-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open ContSet

variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)] {n m : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem NeuralNetwork.holds_robustness {nn : NeuralNetwork S n m} {f : Vec ℝ n → Vec ℝ m}
    (hf : nn.Encloses f) (X : S n) (l : Fin m)
    (u : ∀ j, SupportBound (construct (nn.enclose X))
      (marginDir m j l))
    (h : ∀ j, j ≠ l → (u j).val < 0) : -- --- CONCL ---
    (Specification.unsafeSet (misclassified m l)).Holds (f '' construct X) :=
  hf.holds_of_enclose X _ (disjoint_misclassified_of_bounds l u h)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
