import CORALean.NN.Theorems.MinSuffExplanation
import CORALean.NN.Theorems.MinSuffExplanationAbstract
import CORALean.NN.Theorems.SuffExplanationTransfer

/-!
# Minimality transfers from a network to its abstraction

Split out of `MinSuffExplanationTransfer.lean` (issue #62):
`col:transitive-min-suff-explanation` [1]'s first direction, alongside
`MinSuffExplanationAbstractOfRefined.lean`.

Minimal for `nn` and abstractly sufficient for `nnAbs` gives minimal for
`nnAbs`: a droppable feature there would be droppable at `nn` by transfer.
Both hypotheses are asked for at every `E'`, not only at `E`: minimality is
about the queries one feature down.

## References

* [1] S. Bassan, Y. Y. Elboher, T. Ladner, M. Althoff and G. Katz. "Explaining
      Fast and Slow: Abstraction and Refinement of Provable Explanations".
      ICML 2025.
-/

-- Authors:       Tobias Ladner
-- Written:       06-September-2026
-- Last update:   ---
-- Last revision: ---

namespace CORALean.Real

open ContSet OfInterval

variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)] [OfInterval S] {n m : ℕ}

theorem NeuralNetwork.minSuffExplanationAbstract_of_min (nn nnAbs : NeuralNetwork S n m)
    (x : Vec ℝ n) (ε : ℝ) (E : Finset (Fin n)) (l : Fin m)
    (hcontain : ∀ E' : Finset (Fin n), nn.outputSet (ofInterval (explainBox x ε E'))
      ⊆ construct (nnAbs.propagate (ofInterval (explainBox x ε E'))))
    (hsuffAbs : nnAbs.IsSuffExplanationAbstract x ε E l)
    (hmin : nn.IsMinSuffExplanation x ε E l) :
    nnAbs.IsMinSuffExplanationAbstract x ε E l :=
  ⟨hsuffAbs, fun i hi hdrop =>
    hmin.2 i hi (nn.suffExplanation_of_abstract nnAbs x ε (E \ {i}) l (hcontain _) hdrop)⟩

end CORALean.Real
