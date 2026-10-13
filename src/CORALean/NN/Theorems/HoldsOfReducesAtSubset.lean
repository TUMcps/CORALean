import CORALean.NN.Theorems.ReducesAtOuter
import CORALean.Specification.Theorems.HoldsOfOuter

/-!
# [1, Cor. 2]: a reduced network is reused across subsets

`reducesAt_outer` bounds `f '' construct s` by `nn'.enclose s`, computed once at the
original `s`. Any subset `s' ⊆ construct s` — a branch-and-bound split, say — has its
image inside that same bound, so a specification checked there already holds on `s'`
too, with nothing recomputed: `Layer.enclose_not_monotone` is exactly why recomputing
`nn'.enclose` at `s'` instead would not be sound, and reusing the original bound
sidesteps that rather than needing it.

## References

* [1] T. Ladner and M. Althoff. "Fully Automatic Neural Network Reduction for
      Formal Verification". TMLR. arXiv:2305.01932.
-/

-- Authors:       Claude Opus 5
-- Written:       12-September-2026
-- Last update:   24-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open ContSet

variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)] [∀ n, Plus (S n) (Vec ℝ n)]
  [Mtimes (Mat ℝ) S] [Real.IntervalOuter S] [Real.OfInterval S]


-- =======================================  MAIN THEOREM  ======================================= --

/-- [1, Cor. 2]: a reduced network's enclosure, computed once at `s`, already bounds a
specification check on the image of any subset `s' ⊆ construct s` — no re-derivation of
`ReducesAt` at `s'` needed, and none would help: `Layer.enclose_not_monotone`. -/
theorem NeuralNetwork.holds_of_reducesAt_subset {n m : ℕ} {s : S n} {s' : Set (Vec ℝ n)}
    {nn nn' : NeuralNetwork S n m} {f : Vec ℝ n → Vec ℝ m}
    (h : NeuralNetwork.ReducesAt s nn nn' f) (hsub : s' ⊆ construct s)
    {ContSet : Type} [CORALean.ContSet ContSet (Vec ℝ m)]
    (spec : Specification ContSet) (hspec : spec.Holds (construct (nn'.enclose s))) :
    spec.Holds (f '' s') :=
  spec.holds_of_outer ((Set.image_mono hsub).trans (NeuralNetwork.reducesAt_outer h)) hspec

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
