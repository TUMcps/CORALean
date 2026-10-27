module

public import CORALean.ContSet.Conversion.Real.Instances
public import CORALean.NN.NeuralNetwork
public import CORALean.NN.Operations.ExplainBox
public import CORALean.NN.Definitions.Misclassified
public import CORALean.Specification.Specification

@[expose] public section

/-!
# Sufficient explanation, read at the exact image

[1, Def. 3] read at `image` rather than at `enclose`: separation on the
network's *exact* image of `explainBox`, which is what the paper means by a
refined network's output. Weaker than `IsSuffExplanationAbstract` by
`image_subset`, and it is the conclusion `Specification.holds_of_outer` hands
back from a containment whose left side is an exact image — the shape
`reducesAt_outer` and `neuronMerging_network_outer` prove. Stronger than
`IsSuffExplanation`, which ranges over `construct (explainBox …)` and not over
its `ofInterval` image; `suffExplanation_of_exact` is that step.

## Inputs
* `S` – set representation
* `f` – network function
* `x` – input point
* `ε` – perturbation radius
* `E` – candidate explanation, a feature set
* `l` – target label

## Output
* exact image of the explanation box never lets a rival tie the target

## References

* [1] [S. Bassan, Y. Y. Elboher, T. Ladner, M. Althoff and G. Katz. "Explaining, Fast and Slow:
      Abstraction and Refinement of Provable Explanations". Proceedings of the 42nd International
      Conference on Machine Learning,
      2025.](../../../../references/2025/bassan-icml-explaining-fast-and-slow.md)
-/

-- Authors:       Claude Opus 5
-- Written:       07-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open ContSet Real.OfInterval

variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)] [Real.OfInterval S] {n m : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `E` is sufficient for `nn`'s classification of `x` as `l`, at `nn`'s exact
image of `explainBox`: no point of it lets a rival tie or beat `l`. -/
def IsSuffExplanationExact (S : ℕ → Type) [∀ n, ContSet (S n) (Vec ℝ n)] [Real.OfInterval S]
    (f : Vec ℝ n → Vec ℝ m) (x : Vec ℝ n) (ε : ℝ) (E : Finset (Fin n)) (l : Fin m) : Prop :=
  (Specification.unsafeSet (misclassified m l)).Holds
    (f '' construct (ofInterval (explainBox x ε E) : S n))

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
