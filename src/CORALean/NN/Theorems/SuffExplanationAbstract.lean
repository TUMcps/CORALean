import CORALean.ContSet.Conversion.Real.Interval_to_ContSet
import CORALean.NN.NeuralNetwork
import CORALean.NN.Operations.ExplainBox
import CORALean.NN.Operations.Propagate
import CORALean.NN.Theorems.Misclassified
import CORALean.Specification.Specification

/-!
# Sufficient explanation for an abstract network

`def:suff-explanation-abstract` [1]: `nnAbs` outputs a set, so sufficiency
becomes separation — propagating `explainBox` must never let a rival tie or
beat the target class `l`. This is `disjoint_misclassified_of_bounds`'s
conclusion in the paper's notation: a bound per rival label, each negative, is
exactly "the target's minimum exceeds every rival's maximum".

## References

* [1] S. Bassan, Y. Y. Elboher, T. Ladner, M. Althoff and G. Katz. "Explaining
      Fast and Slow: Abstraction and Refinement of Provable Explanations".
      ICML 2025.
-/

-- Authors:       Tobias Ladner
-- Written:       05-September-2026
-- Last update:   ---
-- Last revision: ---

namespace CORALean.Real

open ContSet OfInterval

variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)] [OfInterval S] {n m : ℕ}

/-- `E` is sufficient for `nnAbs`'s classification of `x` as `l`: propagating
`explainBox`, the output set never lets a rival tie or beat `l`. -/
def NeuralNetwork.IsSuffExplanationAbstract (nnAbs : NeuralNetwork S n m) (x : Vec ℝ n) (ε : ℝ)
    (E : Finset (Fin n)) (l : Fin m) : Prop :=
  (Specification.unsafeSet (misclassified m l)).Holds
    (construct (nnAbs.propagate (ofInterval (explainBox x ε E))))

end CORALean.Real
