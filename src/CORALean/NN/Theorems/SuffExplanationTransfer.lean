import CORALean.NN.Theorems.Misclassified
import CORALean.NN.Theorems.SuffExplanationAbstract
import CORALean.NN.Theorems.SuffExplanation
import CORALean.Specification.Theorems.HoldsOfOuter

/-!
# Transfer: sufficient for the abstract network is sufficient for the original

`col:suff-nn-suff-nnabs` [1]: a sufficient explanation of `nnAbs` is one of `nn`,
given that `nnAbs`'s propagated enclosure of `explainBox` contains `nn`'s exact
image there. The hypothesis `hcontain` is what an abstraction owes.

`SuffExplanationOfNeuronMerging.lean` and `SuffExplanationOfPropagate.lean` are
the two corollaries the refinement loop [1, Alg. 2] actually visits, each
genuinely public and neither the other's helper, so each earns its own file.

## References

* [1] S. Bassan, Y. Y. Elboher, T. Ladner, M. Althoff and G. Katz. "Explaining
      Fast and Slow: Abstraction and Refinement of Provable Explanations".
      ICML 2025.
-/

-- Authors:       Tobias Ladner
-- Written:       05-September-2026
-- Last update:   06-September-2026
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open ContSet OfInterval

variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)] [OfInterval S] {n m : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- Transfer (`col:suff-nn-suff-nnabs` [1]): sufficient for `nnAbs` is sufficient
for `nn`, given that `nnAbs`'s enclosure of `explainBox` contains `nn`'s exact
image there. -/
theorem NeuralNetwork.suffExplanation_of_abstract (nn nnAbs : NeuralNetwork S n m)
    (x : Vec ℝ n) (ε : ℝ) (E : Finset (Fin n)) (l : Fin m)
    (hcontain : nn.outputSet (ofInterval (explainBox x ε E))
      ⊆ construct (nnAbs.propagate (ofInterval (explainBox x ε E))))
    (hsuffAbs : nnAbs.IsSuffExplanationAbstract x ε E l) :
    nn.IsSuffExplanation x ε E l := by -- --- PROOF ---
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


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
