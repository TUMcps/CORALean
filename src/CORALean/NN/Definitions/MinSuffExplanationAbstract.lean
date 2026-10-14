module

public import CORALean.NN.Definitions.SuffExplanationAbstract

@[expose] public section

/-!
# Minimal sufficient explanation for an abstract network

[1, Def. 2] read at the abstract predicate, which is the level [1, Alg. 2]
actually searches at: every query it puts to a verifier is separation on a
enclosed set, never the exact image. Kept apart from `IsMinSuffExplanation`
because minimality is not preserved by transfer — the abstract predicate is the
stronger one, so a set minimal here can still be shrinkable at `nn`.

## References

* [1] S. Bassan, Y. Y. Elboher, T. Ladner, M. Althoff and G. Katz. "Explaining
      Fast and Slow: Abstraction and Refinement of Provable Explanations".
      ICML 2025.
-/

-- Authors:       Claude Opus 5
-- Written:       06-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open ContSet Real.OfInterval

variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)] [Real.OfInterval S] {n m : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- Abstractly sufficient, and no single feature of `E` can be dropped without
losing that. -/
def NeuralNetwork.IsMinSuffExplanationAbstract (nnAbs : NeuralNetwork S n m) (x : Vec ℝ n)
    (ε : ℝ) (E : Finset (Fin n)) (l : Fin m) : Prop :=
  nnAbs.IsSuffExplanationAbstract x ε E l ∧
    ∀ i ∈ E, ¬ nnAbs.IsSuffExplanationAbstract x ε (E \ {i}) l

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
