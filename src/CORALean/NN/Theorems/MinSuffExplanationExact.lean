import CORALean.NN.Theorems.SuffExplanationExact

/-!
# Minimal sufficient explanation, read at the exact image

`def:min-suff-explanation` [1] over `IsSuffExplanationExact`. Kept apart from
`IsMinSuffExplanationAbstract` because the two minimality fields negate
different predicates and the implication between them runs the wrong way: the
exact predicate is the weaker one, so failing it is the stronger statement, and
minimality here does not follow from minimality there. It is the form
`minSuffExplanationExact_of_refined` needs of a refinement, since transfer
along a refinement lands in the exact predicate and nowhere else.

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


-- =====================================  MAIN DEFINITION  ====================================== --

/-- Exactly sufficient, and no single feature of `E` can be dropped without
losing that. -/
def NeuralNetwork.IsMinSuffExplanationExact (nn : NeuralNetwork S n m) (x : Vec ℝ n) (ε : ℝ)
    (E : Finset (Fin n)) (l : Fin m) : Prop :=
  nn.IsSuffExplanationExact x ε E l ∧
    ∀ i ∈ E, ¬ nn.IsSuffExplanationExact x ε (E \ {i}) l

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
