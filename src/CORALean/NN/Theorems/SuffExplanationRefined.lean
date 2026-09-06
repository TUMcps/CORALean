import CORALean.NN.Theorems.Misclassified
import CORALean.NN.Theorems.SuffExplanationAbstract
import CORALean.Specification.Theorems.HoldsOfOuter

/-!
# Refining an abstraction keeps a sufficient explanation sufficient

[1, Prop. 3]: a refinement `nnRef` of `nnAbs` encloses the
query more tightly, and separation survives shrinking. So the explanations
sufficient for `nnAbs` are among those sufficient for `nnRef` — the containment
that makes each refinement step of [1, Alg. 2] able only to *free* further
features, never to lose one already freed.

The other half of the paper's chain, sufficiency for `nnRef` carrying to `nn`,
is `suffExplanation_of_abstract` [2] read at `nnRef`, so it is not restated.
`hrefine` is a containment between two *enclosures* and is satisfied by
`nnRef = nnAbs`; it says nothing about `nn`, which is why nothing here does.

## References

* [1] S. Bassan, Y. Y. Elboher, T. Ladner, M. Althoff and G. Katz. "Explaining
      Fast and Slow: Abstraction and Refinement of Provable Explanations".
      ICML 2025.
* [2] `CORALean.Real.NeuralNetwork.suffExplanation_of_abstract`.
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

/-- Monotonicity along refinement [1, Prop. 3]: what is
sufficient for `nnAbs` stays sufficient for any tighter `nnRef`. -/
theorem NeuralNetwork.suffExplanationAbstract_of_refined (nnAbs nnRef : NeuralNetwork S n m)
    (x : Vec ℝ n) (ε : ℝ) (E : Finset (Fin n)) (l : Fin m)
    (hrefine : construct (nnRef.propagate (ofInterval (explainBox x ε E)))
      ⊆ construct (nnAbs.propagate (ofInterval (explainBox x ε E))))
    (hsuffAbs : nnAbs.IsSuffExplanationAbstract x ε E l) :
    nnRef.IsSuffExplanationAbstract x ε E l :=
  (Specification.unsafeSet (misclassified m l)).holds_of_outer hrefine hsuffAbs

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
