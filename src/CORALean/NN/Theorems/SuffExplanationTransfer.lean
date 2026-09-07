import CORALean.NN.Theorems.Misclassified
import CORALean.NN.Theorems.SuffExplanationAbstract
import CORALean.NN.Theorems.SuffExplanationOfExact
import CORALean.Specification.Theorems.HoldsOfOuter

/-!
# Transfer: sufficient for the abstract network is sufficient for the original

`col:suff-nn-suff-nnabs` [1]: a sufficient explanation of `nnAbs` is one of `nn`,
given that `nnAbs`'s propagated enclosure of `explainBox` contains `nn`'s exact
image there. The hypothesis `hcontain` is what an abstraction owes.

`SuffExplanationOfNeuronMerging.lean` and `SuffExplanationOfPropagate.lean` are
the two corollaries the refinement loop [1, Alg. 2] actually visits, each
genuinely public and neither the other's helper, so each earns its own file.

`hcontain` and `hsuffAbs` compose to `IsSuffExplanationExact`, which is all
`holds_of_outer` gives; `suffExplanation_of_exact` is the second half, reading
that back as the pointwise definition.

## References

* [1] S. Bassan, Y. Y. Elboher, T. Ladner, M. Althoff and G. Katz. "Explaining
      Fast and Slow: Abstraction and Refinement of Provable Explanations".
      ICML 2025.
-/

-- Authors:       Tobias Ladner
-- Written:       05-September-2026
-- Last update:   07-September-2026
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
    nn.IsSuffExplanation x ε E l :=
  nn.suffExplanation_of_exact x ε E l
    ((Specification.unsafeSet (misclassified m l)).holds_of_outer hcontain hsuffAbs)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
