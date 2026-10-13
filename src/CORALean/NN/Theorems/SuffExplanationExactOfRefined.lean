import CORALean.NN.Theorems.Misclassified
import CORALean.NN.Theorems.SuffExplanationAbstract
import CORALean.NN.Theorems.SuffExplanationExact
import CORALean.Specification.Theorems.HoldsOfOuter

/-!
# Refinement keeps a sufficient explanation sufficient, as [1, Prop. 3] states it

The paper compares the refined network's *exact* output with the abstract
network's enclosure: `nnRef` merges fewer neurons than `nnAbs`, and every
merge it does make `nnAbs` makes too, so `nnRef`'s image of `explainBox` lies
inside what `nnAbs` encloses. `hrefine` is that containment, and
`suffExplanationExact_of_reducesAt` discharges it from the merging machinery.

`suffExplanationAbstract_of_refined` is the enclosure-to-enclosure reading
instead. Neither implies the other: `Layer.enclose_not_monotone` blocks
passing from a containment of input sets to one of enclosures, and an exact
image is not an enclosure, so `image_subset` composes in one direction only
— it weakens the enclosure hypothesis to this one, never the reverse.

## References

* [1] S. Bassan, Y. Y. Elboher, T. Ladner, M. Althoff and G. Katz. "Explaining
      Fast and Slow: Abstraction and Refinement of Provable Explanations".
      ICML 2025.
-/

-- Authors:       Claude Opus 5
-- Written:       07-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open ContSet Real.OfInterval

variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)] [Real.OfInterval S] {n m : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- Monotonicity along refinement [1, Prop. 3]: what is abstractly sufficient
for `nnAbs` is exactly sufficient for the refinement `nnRef` it encloses. -/
theorem suffExplanationExact_of_refined (nnAbs : NeuralNetwork S n m)
    (f : Vec ℝ n → Vec ℝ m)
    (x : Vec ℝ n) (ε : ℝ) (E : Finset (Fin n)) (l : Fin m)
    (hrefine : f '' construct (ofInterval (explainBox x ε E) : S n)
      ⊆ construct (nnAbs.enclose (ofInterval (explainBox x ε E))))
    (hsuffAbs : nnAbs.IsSuffExplanationAbstract x ε E l) :
    IsSuffExplanationExact S f x ε E l :=
  (Specification.unsafeSet (misclassified m l)).holds_of_outer hrefine hsuffAbs

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
