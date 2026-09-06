import CORALean.NN.Theorems.MinSuffExplanationAbstract
import CORALean.NN.Theorems.SuffExplanationRefined

/-!
# Minimality transfers from a refinement to the coarser network

Split out of `MinSuffExplanationTransfer.lean` (issue #62):
`col:transitive-min-suff-explanation` [1]'s other direction, alongside
`MinSuffExplanationAbstractOfMin.lean`.

Minimal for a refinement `nnRef` gives minimal for the coarser `nnAbs`: a
droppable feature there would be droppable at `nnRef` by monotonicity.

## References

* [1] S. Bassan, Y. Y. Elboher, T. Ladner, M. Althoff and G. Katz. "Explaining
      Fast and Slow: Abstraction and Refinement of Provable Explanations".
      ICML 2025.
-/

-- Authors:       Tobias Ladner
-- Written:       06-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open ContSet OfInterval

variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)] [OfInterval S] {n m : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem NeuralNetwork.minSuffExplanationAbstract_of_refined (nnAbs nnRef : NeuralNetwork S n m)
    (x : Vec ℝ n) (ε : ℝ) (E : Finset (Fin n)) (l : Fin m)
    (hrefine : ∀ E' : Finset (Fin n),
      construct (nnRef.propagate (ofInterval (explainBox x ε E')))
        ⊆ construct (nnAbs.propagate (ofInterval (explainBox x ε E'))))
    (hsuffAbs : nnAbs.IsSuffExplanationAbstract x ε E l)
    (hmin : nnRef.IsMinSuffExplanationAbstract x ε E l) :
    nnAbs.IsMinSuffExplanationAbstract x ε E l :=
  ⟨hsuffAbs, fun i hi hdrop =>
    hmin.2 i hi (NeuralNetwork.suffExplanationAbstract_of_refined nnAbs nnRef x ε (E \ {i}) l
      (hrefine _) hdrop)⟩

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
