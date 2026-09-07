import CORALean.NN.Theorems.ReducesAtOuter
import CORALean.NN.Theorems.SuffExplanationExactOfRefined

/-!
# The refinement hypothesis, discharged by neuron merging

What makes [1, Prop. 3] usable: `nnAbs` merges everything `nnRef` merges and
more, which is exactly `ReducesAt` [2] with `nnRef` in the role of the original
network, and then `reducesAt_outer` is the containment
`suffExplanationExact_of_refined` asks for. So a caller who reached `nnAbs` by
merging neurons supplies a derivation, not a set containment.

`ReducesAt` is indexed by the input set each layer is reduced over, and here
that index is `ofInterval (explainBox x ε E)` itself, so the two line up with
no side condition: the `hY` look-ahead inside the derivation is already stated
over the propagated `explainBox`.

## References

* [1] S. Bassan, Y. Y. Elboher, T. Ladner, M. Althoff and G. Katz. "Explaining
      Fast and Slow: Abstraction and Refinement of Provable Explanations".
      ICML 2025.
* [2] `CORALean.Real.NeuralNetwork.ReducesAt`.
-/

-- Authors:       Tobias Ladner
-- Written:       07-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix ContSet Plus Mtimes IntervalOuter OfInterval

variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)] [∀ n, Plus (S n) (Vec ℝ n)]
  [Mtimes (Mat ℝ) S] [IntervalOuter S] [OfInterval S] {n m : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- Abstractly sufficient for a reduction `nnAbs` of `nnRef` is exactly
sufficient for `nnRef`, with no containment asked of the caller. -/
theorem NeuralNetwork.suffExplanationExact_of_reducesAt (nnRef nnAbs : NeuralNetwork S n m)
    (x : Vec ℝ n) (ε : ℝ) (E : Finset (Fin n)) (l : Fin m)
    (hred : NeuralNetwork.ReducesAt (ofInterval (explainBox x ε E)) nnRef nnAbs)
    (hsuffAbs : nnAbs.IsSuffExplanationAbstract x ε E l) :
    nnRef.IsSuffExplanationExact x ε E l :=
  NeuralNetwork.suffExplanationExact_of_refined nnAbs nnRef x ε E l
    (NeuralNetwork.reducesAt_outer hred) hsuffAbs

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
