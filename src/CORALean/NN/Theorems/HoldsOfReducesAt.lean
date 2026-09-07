import CORALean.NN.Theorems.ReducesAtOuter
import CORALean.Specification.Theorems.HoldsOfOuter

/-!
# [1, Thm. 1]: verifying the reduced network entails verifying the original

Three lines, because `reducesAt_outer` already did the work: a specification checked on the
reduced network's enclosure holds on the original network's exact image, by
`Specification.holds_of_outer` at the containment `reducesAt_outer` proves.

## References

* [1] T. Ladner and M. Althoff. "Fully Automatic Neural Network Reduction for
      Formal Verification". TMLR. arXiv:2305.01932.
-/

-- Authors:       Tobias Ladner
-- Written:       06-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open ContSet

variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)] [∀ n, Plus (S n) (Vec ℝ n)]
  [Mtimes (Mat ℝ) S] [IntervalOuter S] [OfInterval S]


-- =======================================  MAIN THEOREM  ======================================= --

/-- [1, Thm. 1]: a specification holding on the reduced network's enclosure holds on the
original network's exact image, at any set of layers reduced. -/
theorem NeuralNetwork.holds_of_reducesAt {n m : ℕ} {s : S n} {nn nn' : NeuralNetwork S n m}
    (h : NeuralNetwork.ReducesAt s nn nn') (spec : Specification (Vec ℝ m))
    (hspec : spec.Holds (construct (nn'.enclose s))) : spec.Holds (nn.image (construct s)) :=
  spec.holds_of_outer (NeuralNetwork.reducesAt_outer h) hspec

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
