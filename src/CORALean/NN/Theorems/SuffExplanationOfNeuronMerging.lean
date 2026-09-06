import CORALean.NN.Theorems.NeuronMergingNetworkOuter
import CORALean.NN.Theorems.SuffExplanationTransfer

/-!
# Transfer at a network the abstraction actually produces

Split out of `SuffExplanationTransfer.lean` (issue #62): one of the two
corollaries the refinement loop [1, Alg. 2] actually visits, alongside
`SuffExplanationOfPropagate.lean` — merging the bucket `part.right` at one
layer, `hcontain` is `neuronMerging_network_outer` [2] and nothing further is
assumed.

## References

* [1] S. Bassan, Y. Y. Elboher, T. Ladner, M. Althoff and G. Katz. "Explaining
      Fast and Slow: Abstraction and Refinement of Provable Explanations".
      ICML 2025.
* [2] `CORALean.Real.neuronMerging_network_outer`.
-/

-- Authors:       Tobias Ladner
-- Written:       06-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix ContSet Plus Mtimes IntervalOuter OfInterval

variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)] [OfInterval S] {n m : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem NeuralNetwork.suffExplanation_of_neuronMerging [∀ n, Plus (S n) (Vec ℝ n)]
    [Mtimes (Mat ℝ) S] [IntervalOuter S] {n₀ n₁ nk n₂ n₃ d r : ℕ}
    (pre : NeuralNetwork S n₀ n₁) (post : NeuralNetwork S n₂ n₃)
    (part : Split (Fin nk) into (Fin d) and (Fin r))
    (W0 : Mat ℝ nk n₁) (b0 : Vec ℝ nk) {σ : ℝ → ℝ} (R : Relaxation σ)
    (W1 : Mat ℝ n₂ nk) (b1 : Vec ℝ n₂) (Y : Interval (Vec ℝ nk))
    (x : Vec ℝ n₀) (ε : ℝ) (E : Finset (Fin n₀)) (l : Fin n₃)
    (hY : ∀ z ∈ construct (pre.propagate (ofInterval (explainBox x ε E))),
      (fun i => σ ((W0 *ᵥ z + b0) i)) ∈ construct Y)
    -- the reduced network: both linear layers trimmed to `part.left`, the bucket boxed into `k+1`
    (hsuffAbs : (NeuralNetwork.cons pre.toLayer
        (.cons (Layer.linear (W0.submatrix part.left id) (b0 ∘ part.left))
          (.cons (Layer.activation R)
            (.cons (Layer.linearWithError (W1.submatrix id part.left) b1
                (Interval.mtimes (W1.submatrix id part.right)
                  ⟨Y.inf ∘ part.right, Y.sup ∘ part.right⟩)
                (Interval.mtimes_isNonempty _ _))
              post)))).IsSuffExplanationAbstract x ε E l) :
    -- and the original, whose exact image `neuronMerging_network_outer` puts inside it
    (NeuralNetwork.cons pre.toLayer
        (.cons (Layer.linear W0 b0)
          (.cons (Layer.activation R)
            (.cons (Layer.linear W1 b1) post)))).IsSuffExplanation x ε E l :=
  NeuralNetwork.suffExplanation_of_abstract _ _ x ε E l
    (neuronMerging_network_outer pre post part W0 b0 R W1 b1 Y
      (ofInterval (explainBox x ε E)) hY) hsuffAbs

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
