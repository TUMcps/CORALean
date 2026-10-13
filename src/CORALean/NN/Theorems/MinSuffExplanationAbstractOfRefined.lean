module

public import CORALean.NN.Theorems.MinSuffExplanationAbstract
public import CORALean.NN.Theorems.SuffExplanationRefined

@[expose] public section

/-!
# Minimality transfers from a refinement to the coarser network

Split out of `MinSuffExplanationTransfer.lean` (issue #62): [1, Prop. 4]'s other
direction, alongside `MinSuffExplanationAbstractOfMin.lean`.

Minimal for a refinement `nnRef` gives minimal for the coarser `nnAbs`: a
droppable feature there would be droppable at `nnRef` by monotonicity.

`hrefine` is the enclosure-to-enclosure containment, so this reads
`suffExplanationAbstract_of_refined`. `minSuffExplanationExact_of_refined` is
the same corollary under the containment [1, Prop. 2] states, and needs
`nnRef`'s minimality in the exact predicate to match what transfer lands in.

## References

* [1] S. Bassan, Y. Y. Elboher, T. Ladner, M. Althoff and G. Katz. "Explaining
      Fast and Slow: Abstraction and Refinement of Provable Explanations".
      ICML 2025.
-/

-- Authors:       Claude Opus 5
-- Written:       06-September-2026
-- Last update:   07-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open ContSet Real.OfInterval

variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)] [Real.OfInterval S] {n m : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem NeuralNetwork.minSuffExplanationAbstract_of_refined (nnAbs nnRef : NeuralNetwork S n m)
    (x : Vec ℝ n) (ε : ℝ) (E : Finset (Fin n)) (l : Fin m)
    (hrefine : ∀ E' : Finset (Fin n),
      construct (nnRef.enclose (ofInterval (explainBox x ε E')))
        ⊆ construct (nnAbs.enclose (ofInterval (explainBox x ε E'))))
    (hsuffAbs : nnAbs.IsSuffExplanationAbstract x ε E l)
    (hmin : nnRef.IsMinSuffExplanationAbstract x ε E l) :
    nnAbs.IsMinSuffExplanationAbstract x ε E l :=
  ⟨hsuffAbs, fun i hi hdrop =>
    hmin.2 i hi (NeuralNetwork.suffExplanationAbstract_of_refined nnAbs nnRef x ε (E \ {i}) l
      (hrefine _) hdrop)⟩

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
