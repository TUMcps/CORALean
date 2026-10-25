module

public import CORALean.NN.Theorems.ReducesAtOuter
public import CORALean.NN.Theorems.SuffExplanationExactOfRefined

@[expose] public section

/-!
# The refinement hypothesis, discharged by neuron merging

What makes [1, Prop. 3] usable: `nnAbs` merges everything `nnRef` merges and more, which is exactly
`ReducesAt` [2] with `nnRef` in the role of the original network, and then `reducesAt_outer` is the
containment `suffExplanationExact_of_refined` asks for. So a caller who reached `nnAbs` by merging
neurons supplies a derivation, not a set containment. `ReducesAt` is indexed by the input set each
layer is reduced over, here `ofInterval (explainBox x ε E)` itself, so the two line up with no side
condition.

## Inputs
* `nnRef` – refined network
* `nnAbs` – coarser network
* `f` – map the refined network encloses
* `x` – input point
* `ε` – perturbation radius
* `E` – explanation, a feature set
* `l` – target label

## Hypotheses
* `hred` – the coarser network reduces the refined one
* `hsuffAbs` – the explanation is abstractly sufficient for the coarser network

## Conclusion
* the explanation is exactly sufficient

## References

* [1] S. Bassan, Y. Y. Elboher, T. Ladner, M. Althoff and G. Katz. "Explaining, Fast and Slow:
      Abstraction and Refinement of Provable Explanations". Proceedings of the 42nd International
      Conference on Machine Learning, 2025.
* [2] `CORALean.NeuralNetwork.ReducesAt`.
-/

-- Authors:       Claude Opus 5
-- Written:       07-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix ContSet Plus Mtimes Real.IntervalOuter Real.OfInterval

variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)] [∀ n, Plus (S n) (Vec ℝ n)]
  [Mtimes (Mat ℝ) S] [Real.IntervalOuter S] [Real.OfInterval S] {n m : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- Abstractly sufficient for a reduction `nnAbs` of `nnRef` is exactly
sufficient for `nnRef`, with no containment asked of the caller. -/
theorem NeuralNetwork.suffExplanationExact_of_reducesAt {nnRef nnAbs : NeuralNetwork S n m}
    {f : Vec ℝ n → Vec ℝ m}
    (x : Vec ℝ n) (ε : ℝ) (E : Finset (Fin n)) (l : Fin m)
    (hred : NeuralNetwork.ReducesAt (ofInterval (explainBox x ε E)) nnRef nnAbs f)
    (hsuffAbs : nnAbs.IsSuffExplanationAbstract x ε E l) :
    IsSuffExplanationExact S f x ε E l :=
  suffExplanationExact_of_refined nnAbs f x ε E l
    (NeuralNetwork.reducesAt_outer hred) hsuffAbs

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
