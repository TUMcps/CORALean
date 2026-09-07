import CORALean.NN.Theorems.ImageSubset
import CORALean.Specification.Theorems.HoldsOfOuter
import CORALean.Specification.Theorems.HoldsAllOfOuter

/-!
# Verification against a whole list, at the propagated set

Split out of `Verified.lean` (issue #62), renamed to match: the same transfer
as `HoldsOfPropagate.lean`, `holds_of_outer` traded for `Specification.
HoldsAll`'s own `holdsAll_of_outer`.
-/

-- Authors:       Tobias Ladner
-- Written:       02-September-2026
-- Last update:   06-September-2026
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open ContSet

variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)] {n m : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem NeuralNetwork.holdsAll_of_propagate (nn : NeuralNetwork S n m) (X : S n)
    (specs : List (Specification (Vec ℝ m)))
    (h : Specification.HoldsAll specs (construct (nn.propagate X))) :
    Specification.HoldsAll specs (nn.image (construct X)) :=
  Specification.holdsAll_of_outer specs (nn.image_subset X) h

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
