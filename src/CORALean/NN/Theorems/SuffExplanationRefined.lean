import CORALean.NN.Theorems.Misclassified
import CORALean.NN.Theorems.SuffExplanationAbstract
import CORALean.Specification.Theorems.HoldsOfOuter

/-!
# Refining an abstraction, enclosure to enclosure

Both sides here are *enclosures*: `nnRef`'s propagated set sits inside
`nnAbs`'s, so separation survives the shrinking and what is sufficient for
`nnAbs` is sufficient for `nnRef` — what lets each refinement step of
[1, Alg. 2] only *free* further features, never lose one already freed.

Not the containment [1, Prop. 3] states, which compares `nnRef`'s exact output
with `nnAbs`'s enclosure; that is `suffExplanationExact_of_refined`, and
neither reading implies the other. `hrefine` is nothing neuron merging
produces — it suits a propagation technique whose enclosures nest, as CORA's
zonotope propagation does inside the interval look-ahead a merge uses. It is
satisfied by `nnRef = nnAbs` and says nothing about `nn`, which is why nothing
here does.

## References

* [1] S. Bassan, Y. Y. Elboher, T. Ladner, M. Althoff and G. Katz. "Explaining
      Fast and Slow: Abstraction and Refinement of Provable Explanations".
      ICML 2025.
-/

-- Authors:       Tobias Ladner
-- Written:       06-September-2026
-- Last update:   07-September-2026
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open ContSet OfInterval

variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)] [OfInterval S] {n m : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- Monotonicity along refinement: what is abstractly sufficient for `nnAbs`
stays so for any `nnRef` whose enclosure `nnAbs`'s contains. -/
theorem NeuralNetwork.suffExplanationAbstract_of_refined (nnAbs nnRef : NeuralNetwork S n m)
    (x : Vec ℝ n) (ε : ℝ) (E : Finset (Fin n)) (l : Fin m)
    (hrefine : construct (nnRef.propagate (ofInterval (explainBox x ε E)))
      ⊆ construct (nnAbs.propagate (ofInterval (explainBox x ε E))))
    (hsuffAbs : nnAbs.IsSuffExplanationAbstract x ε E l) :
    nnRef.IsSuffExplanationAbstract x ε E l :=
  (Specification.unsafeSet (misclassified m l)).holds_of_outer hrefine hsuffAbs

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
