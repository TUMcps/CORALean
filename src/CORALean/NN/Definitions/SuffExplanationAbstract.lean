module

public import CORALean.ContSet.Conversion.Real.Instances
public import CORALean.NN.NeuralNetwork
public import CORALean.NN.Operations.ExplainBox
public import CORALean.NN.Operations.Enclose
public import CORALean.NN.Definitions.Misclassified
public import CORALean.Specification.Specification

@[expose] public section

/-!
# Sufficient explanation for an abstract network

[1, Def. 3]: `nnAbs` outputs a set, so sufficiency becomes separation — propagating `explainBox`
must never let a rival tie or beat the target class `l`. This is
`disjoint_misclassified_of_bounds`'s conclusion in the paper's notation.

[1, Def. 4] renames this same predicate rather than adding to it: a sufficient explanation for
`nnAbs` is called an *abstract* sufficient explanation for whatever network `nnAbs` abstracts,
without changing what it asks of `nnAbs` itself.

## Inputs
* `nnAbs` – abstract network
* `x` – input point
* `ε` – perturbation radius
* `E` – candidate explanation, a feature set
* `l` – target label

## Output
* enclosure of the explanation box never lets a rival tie the target

## References

* [1] S. Bassan, Y. Y. Elboher, T. Ladner, M. Althoff and G. Katz. "Explaining, Fast and Slow:
      Abstraction and Refinement of Provable Explanations". Proceedings of the 42nd International
      Conference on Machine Learning, 2025.
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
