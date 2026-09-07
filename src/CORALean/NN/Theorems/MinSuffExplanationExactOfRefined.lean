import CORALean.NN.Theorems.MinSuffExplanationAbstract
import CORALean.NN.Theorems.MinSuffExplanationExact
import CORALean.NN.Theorems.SuffExplanationExactOfRefined

/-!
# Minimality transfers from a refinement to the coarser network

`col:transitive-min-suff-explanation` [1] beside
`MinSuffExplanationAbstractOfRefined.lean`, stated against the containment
[1, Prop. 3] actually asks for: a droppable feature at `nnAbs` would be
droppable at `nnRef` too.

Transfer runs from the abstract predicate into the exact one, so the
refinement's minimality has to negate the exact predicate — `hmin` is
`IsMinSuffExplanationExact` and not `IsMinSuffExplanationAbstract`, which would
leave `hmin.2` and the transferred sufficiency in different predicates with the
implication between them pointing the wrong way.

## References

* [1] S. Bassan, Y. Y. Elboher, T. Ladner, M. Althoff and G. Katz. "Explaining
      Fast and Slow: Abstraction and Refinement of Provable Explanations".
      ICML 2025.
-/

-- Authors:       Tobias Ladner
-- Written:       07-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open ContSet OfInterval

variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)] [OfInterval S] {n m : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- Minimal for the refinement `nnRef` gives minimal for the coarser `nnAbs`,
under the containment [1, Prop. 3] states. -/
theorem NeuralNetwork.minSuffExplanationExact_of_refined (nnAbs nnRef : NeuralNetwork S n m)
    (x : Vec ℝ n) (ε : ℝ) (E : Finset (Fin n)) (l : Fin m)
    (hrefine : ∀ E' : Finset (Fin n), nnRef.image (construct (ofInterval (explainBox x ε E') : S n))
      ⊆ construct (nnAbs.propagate (ofInterval (explainBox x ε E'))))
    (hsuffAbs : nnAbs.IsSuffExplanationAbstract x ε E l)
    (hmin : nnRef.IsMinSuffExplanationExact x ε E l) :
    nnAbs.IsMinSuffExplanationAbstract x ε E l :=
  ⟨hsuffAbs, fun i hi hdrop =>
    hmin.2 i hi (NeuralNetwork.suffExplanationExact_of_refined nnAbs nnRef x ε (E \ {i}) l
      (hrefine _) hdrop)⟩

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
