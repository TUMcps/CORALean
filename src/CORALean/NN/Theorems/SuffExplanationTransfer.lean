module

public import CORALean.NN.Definitions.Misclassified
public import CORALean.NN.Definitions.SuffExplanationAbstract
public import CORALean.NN.Theorems.SuffExplanationOfExact
public import CORALean.Specification.Theorems.HoldsOfOuter

@[expose] public section

/-!
# Transfer: sufficient for the abstract network is sufficient for the original

[1, Prop. 1]: a sufficient explanation of `nnAbs` is one of `nn`, given that `nnAbs`'s enclosure of
`explainBox` contains `nn`'s exact image there. The hypothesis `hcontain` is what an abstraction
owes. `SuffExplanationOfNeuronMerging.lean` and `SuffExplanationOfEnclose.lean` are the two
corollaries the refinement loop [1, Alg. 2] actually visits, each public and neither the other's
helper. `hcontain` and `hsuffAbs` compose to `IsSuffExplanationExact`, which is all `holds_of_outer`
gives; `suffExplanation_of_exact` reads that back as the pointwise definition.

## Inputs
* `f` – network function
* `nnAbs` – abstract network
* `x` – input point
* `ε` – perturbation radius
* `E` – explanation, a feature set
* `l` – target label

## Hypotheses
* `hcontain` – the abstract enclosure contains the exact image
* `hsuffAbs` – the explanation is abstractly sufficient

## Conclusion
* the explanation is sufficient for the network function

## References

* [1] S. Bassan, Y. Y. Elboher, T. Ladner, M. Althoff and G. Katz. "Explaining
      Fast and Slow: Abstraction and Refinement of Provable Explanations".
      ICML 2025.
-/

-- Authors:       Claude Opus 5
-- Written:       05-September-2026
-- Last update:   07-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open ContSet Real.OfInterval

variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)] [Real.OfInterval S] {n m : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- Transfer ([1, Prop. 1]): sufficient for `nnAbs` is sufficient for `nn`,
given that `nnAbs`'s enclosure of `explainBox` contains `nn`'s exact image
there. -/
theorem suffExplanation_of_abstract (f : Vec ℝ n → Vec ℝ m) (nnAbs : NeuralNetwork S n m)
    (x : Vec ℝ n) (ε : ℝ) (E : Finset (Fin n)) (l : Fin m)
    (hcontain : f '' construct (ofInterval (explainBox x ε E) : S n)
      ⊆ construct (nnAbs.enclose (ofInterval (explainBox x ε E))))
    (hsuffAbs : nnAbs.IsSuffExplanationAbstract x ε E l) :
    IsSuffExplanation f x ε E l :=
  suffExplanation_of_exact f x ε E l
    ((Specification.unsafeSet (misclassified m l)).holds_of_outer hcontain hsuffAbs)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
