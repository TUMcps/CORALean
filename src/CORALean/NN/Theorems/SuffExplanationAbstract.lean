import CORALean.ContSet.Conversion.Real.Interval_to_ContSet
import CORALean.NN.NeuralNetwork
import CORALean.NN.Operations.ExplainBox
import CORALean.NN.Operations.Enclose
import CORALean.NN.Theorems.Misclassified
import CORALean.Specification.Specification

/-!
# Sufficient explanation for an abstract network

[1, Def. 3]: `nnAbs` outputs a set, so sufficiency becomes separation —
propagating `explainBox` must never let a rival tie or beat the target class
`l`. This is `disjoint_misclassified_of_bounds`'s conclusion in the paper's
notation: a bound per rival label, each negative, is exactly "the target's
minimum exceeds every rival's maximum".

[1, Def. 4] renames this same predicate rather than adding to it: a
sufficient explanation for `nnAbs` is called an *abstract* sufficient
explanation for whatever network `nnAbs` abstracts, without changing what it
asks of `nnAbs` itself — so it is `IsSuffExplanationAbstract` again, read at
the abstraction rather than at the network it abstracts.

## References

* [1] S. Bassan, Y. Y. Elboher, T. Ladner, M. Althoff and G. Katz. "Explaining
      Fast and Slow: Abstraction and Refinement of Provable Explanations".
      ICML 2025.
-/

-- Authors:       Claude Opus 5
-- Written:       05-September-2026
-- Last update:   12-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open ContSet Real.OfInterval

variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)] [Real.OfInterval S] {n m : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `E` is sufficient for `nnAbs`'s classification of `x` as `l`: propagating
`explainBox`, the image never lets a rival tie or beat `l`. -/
def NeuralNetwork.IsSuffExplanationAbstract (nnAbs : NeuralNetwork S n m) (x : Vec ℝ n) (ε : ℝ)
    (E : Finset (Fin n)) (l : Fin m) : Prop :=
  (Specification.unsafeSet (misclassified m l)).Holds
    (construct (nnAbs.enclose (ofInterval (explainBox x ε E))))

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
