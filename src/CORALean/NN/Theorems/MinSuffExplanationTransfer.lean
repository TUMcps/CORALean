import CORALean.NN.Theorems.MinSuffExplanation
import CORALean.NN.Theorems.MinSuffExplanationAbstract
import CORALean.NN.Theorems.SuffExplanationRefined
import CORALean.NN.Theorems.SuffExplanationTransfer

/-!
# Minimality travels the way sufficiency does not

`col:transitive-min-suff-explanation` [1]: minimality is a statement about what
*fails*, so each implication of it is the contrapositive of a sufficiency
transfer at `E \ {i}` — and the chain therefore runs against the one sufficiency
takes. Minimal for `nn` gives minimal for the abstraction; minimal for a
refinement gives minimal for the coarser network it came from.

Both hypotheses are asked for at every `E'`, not only at `E`: minimality is
about the queries one feature down, and an abstraction sound at `E` says nothing
about them. Neither is vacuous — `nnAbs = nn` and `nnRef = nnAbs` satisfy them.

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

/-- Minimal for `nn` and abstractly sufficient for `nnAbs` gives minimal for
`nnAbs`: a droppable feature there would be droppable at `nn` by transfer. -/
theorem NeuralNetwork.minSuffExplanationAbstract_of_min (nn nnAbs : NeuralNetwork S n m)
    (x : Vec ℝ n) (ε : ℝ) (E : Finset (Fin n)) (l : Fin m)
    (hcontain : ∀ E' : Finset (Fin n), nn.outputSet (ofInterval (explainBox x ε E'))
      ⊆ construct (nnAbs.propagate (ofInterval (explainBox x ε E'))))
    (hsuffAbs : nnAbs.IsSuffExplanationAbstract x ε E l)
    (hmin : nn.IsMinSuffExplanation x ε E l) :
    nnAbs.IsMinSuffExplanationAbstract x ε E l :=
  ⟨hsuffAbs, fun i hi hdrop =>
    hmin.2 i hi (nn.suffExplanation_of_abstract nnAbs x ε (E \ {i}) l (hcontain _) hdrop)⟩

/-- Minimal for a refinement `nnRef` gives minimal for the coarser `nnAbs`: a
droppable feature there would be droppable at `nnRef` by monotonicity. -/
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
