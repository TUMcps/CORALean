module

public import CORALean.NN.Definitions.MinSuffExplanation
public import CORALean.NN.Definitions.MinSuffExplanationAbstract
public import CORALean.NN.Theorems.SuffExplanationTransfer

@[expose] public section

/-!
# Minimality transfers from a network to its abstraction

Split out of `MinSuffExplanationTransfer.lean` (issue #62): [1, Prop. 4]'s first
direction, alongside `MinSuffExplanationAbstractOfRefined.lean`.

Minimal for `nn` and abstractly sufficient for `nnAbs` gives minimal for
`nnAbs`: a droppable feature there would be droppable at `nn` by transfer. Both
hypotheses are asked for at every `E'`, not only at `E`: minimality is about the
queries one feature down.

## Inputs
* `f` – network function
* `nnAbs` – abstract network
* `x` – input point
* `ε` – perturbation radius
* `E` – explanation, a feature set
* `l` – target label

## Hypotheses
* `hcontain` – the abstract network's enclosure contains the exact image
* `hsuffAbs` – the explanation is abstractly sufficient
* `hmin` – the explanation is minimal for the network function

## Conclusion
* the explanation is minimal for the abstract network

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


-- =======================================  MAIN THEOREM  ======================================= --

theorem NeuralNetwork.minSuffExplanationAbstract_of_min (f : Vec ℝ n → Vec ℝ m)
    (nnAbs : NeuralNetwork S n m)
    (x : Vec ℝ n) (ε : ℝ) (E : Finset (Fin n)) (l : Fin m)
    (hcontain : ∀ E' : Finset (Fin n), f '' construct (ofInterval (explainBox x ε E') : S n)
      ⊆ construct (nnAbs.enclose (ofInterval (explainBox x ε E'))))
    (hsuffAbs : nnAbs.IsSuffExplanationAbstract x ε E l)
    (hmin : IsMinSuffExplanation f x ε E l) : -- --- CONCL ---
    nnAbs.IsMinSuffExplanationAbstract x ε E l :=
  ⟨hsuffAbs, fun i hi hdrop =>
    hmin.2 i hi (suffExplanation_of_abstract f nnAbs x ε (E \ {i}) l (hcontain _) hdrop)⟩

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
