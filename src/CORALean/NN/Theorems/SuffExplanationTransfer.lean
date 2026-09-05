import CORALean.NN.Theorems.SuffExplanationAbstract
import CORALean.NN.Theorems.SuffExplanation

/-!
# Transfer: sufficient for the abstract network is sufficient for the original

`col:suff-nn-suff-nnabs` [1]: a sufficient explanation of `nnAbs` is one of `nn`,
given that `nnAbs`'s propagated enclosure of `explainBox` contains `nn`'s exact
image there — the shape `neuronMerging_sandwich_outer` [2] proves for one merged
sandwich. Generalising it to a whole network is that theorem's job, not this
one's: it is stated here only as the hypothesis `hcontain`.

Set-level throughout, so there is no float counterpart here, exactly as for
`neuronMerging_sandwich_outer`.

## References

* [1] S. Bassan, Y. Y. Elboher, T. Ladner, M. Althoff and G. Katz. "Explaining
      Fast and Slow: Abstraction and Refinement of Provable Explanations".
      ICML 2025.
* [2] `CORALean.Real.neuronMerging_sandwich_outer`.
-/

-- Authors:       Tobias Ladner
-- Written:       05-September-2026
-- Last update:   ---
-- Last revision: ---

namespace CORALean.Real

open ContSet OfInterval

variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)] [OfInterval S] {n m : ℕ}

/-- Transfer (`col:suff-nn-suff-nnabs` [1]): sufficient for `nnAbs` is sufficient
for `nn`, given that `nnAbs`'s enclosure of `explainBox` contains `nn`'s exact
image there. -/
theorem NeuralNetwork.suffExplanation_of_abstract (nn nnAbs : NeuralNetwork S n m)
    (x : Vec ℝ n) (ε : ℝ) (E : Finset (Fin n)) (l : Fin m)
    (hcontain : nn.outputSet (ofInterval (explainBox x ε E))
      ⊆ construct (nnAbs.propagate (ofInterval (explainBox x ε E))))
    (hsuffAbs : nnAbs.IsSuffExplanationAbstract x ε E l) :
    nn.IsSuffExplanation x ε E l := by
  have hspec : (Specification.unsafeSet (misclassified m l)).Holds
      (nn.outputSet (ofInterval (explainBox x ε E))) :=
    (Specification.unsafeSet (misclassified m l)).holds_of_outer hcontain hsuffAbs
  intro x' hx' j hj
  have hmem : nn.eval x' ∈ nn.outputSet (ofInterval (explainBox x ε E)) :=
    ⟨x', ofInterval_outer _ hx', rfl⟩
  have hd := Set.disjoint_left.mp hspec hmem
  by_contra hc
  exact hd ⟨j, hj, not_lt.mp hc⟩

end CORALean.Real
