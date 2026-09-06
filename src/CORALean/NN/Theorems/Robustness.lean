import CORALean.NN.Theorems.DisjointMisclassifiedOfBounds
import CORALean.NN.Theorems.MarginDir
import CORALean.NN.Theorems.Misclassified
import CORALean.NN.Theorems.HoldsOfPropagate

/-!
# Robust classification, as a specification the outputs avoid

The requirement a classifier is normally verified against: over a whole input
set — an image and everything within a perturbation of it — the same label wins.
Written as an unsafe set, since what must not happen is that some other label
catches up, and then it is checked by the same theorem everything else is.
-/

-- Authors:       Tobias Ladner
-- Written:       02-September-2026
-- Last update:   ---
-- Last revision: ---

namespace CORALean.Real

open ContSet

variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)] {n m : ℕ}

theorem NeuralNetwork.holds_robustness (nn : NeuralNetwork S n m) (X : S n) (l : Fin m)
    (u : ∀ j, SupportBound (construct (nn.propagate X))
      (marginDir m j l))
    (h : ∀ j, j ≠ l → (u j).val < 0) :
    (Specification.unsafeSet (misclassified m l)).Holds (nn.outputSet X) :=
  nn.holds_of_propagate X _ (disjoint_misclassified_of_bounds l u h)

end CORALean.Real
