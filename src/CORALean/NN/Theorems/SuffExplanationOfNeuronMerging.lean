import CORALean.NN.Theorems.NeuronMergingNetworkOuter
import CORALean.NN.Theorems.SuffExplanationTransfer

/-!
# Transfer at a network the abstraction actually produces

Split out of `SuffExplanationTransfer.lean` (issue #62): one of the two
corollaries the refinement loop [1, Alg. 2] actually visits, alongside
`SuffExplanationOfEnclose.lean` — merging the bucket `part.right` at one
layer, `hcontain` is `neuronMerging_network_outer` [2] and nothing further is
assumed.

## References

* [1] S. Bassan, Y. Y. Elboher, T. Ladner, M. Althoff and G. Katz. "Explaining
      Fast and Slow: Abstraction and Refinement of Provable Explanations".
      ICML 2025.
* [2] `CORALean.neuronMerging_network_outer`.
-/

-- Authors:       Tobias Ladner
-- Written:       06-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix ContSet Plus Mtimes Real.IntervalOuter Real.OfInterval

variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)] [Real.OfInterval S] {n m : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem NeuralNetwork.suffExplanation_of_neuronMerging [∀ n, Plus (S n) (Vec ℝ n)]
    [Mtimes (Mat ℝ) S] [Real.IntervalOuter S] {n₀ n₁ nk n₂ n₃ d r : ℕ}
    (pre : NeuralNetwork S n₀ n₁) (post : NeuralNetwork S n₂ n₃)
    (part : Split (Fin nk) into (Fin d) ⊕ (Fin r))
    (W0 : Mat ℝ nk n₁) (b0 : Vec ℝ nk) {σ : ℝ → ℝ} (R : Real.Relaxation σ)
    (W1 : Mat ℝ n₂ nk) (b1 : Vec ℝ n₂) (Y : Real.Interval (Vec ℝ nk))
    (x : Vec ℝ n₀) (ε : ℝ) (E : Finset (Fin n₀)) (l : Fin n₃)
    {fpre : Vec ℝ n₀ → Vec ℝ n₁} (hpre : pre.Sound fpre)
    {fpost : Vec ℝ n₂ → Vec ℝ n₃} (hpost : post.Sound fpost)
    (hY : ∀ z ∈ construct (pre.enclose (ofInterval (explainBox x ε E))),
      (fun i => σ ((W0 *ᵥ z + b0) i)) ∈ construct Y)
    -- the reduced network: both linear layers trimmed to `part.left`, the bucket boxed into `k+1`
    (hsuffAbs : (NeuralNetwork.cons pre.toLayer
        (.cons (Real.Layer.linear (W0.submatrix part.left id) (b0 ∘ part.left))
          (.cons (Real.Layer.activation R)
            (.cons (Real.Layer.linearWithError (W1.submatrix id part.left) b1
                (Real.Interval.mtimes (W1.submatrix id part.right)
                  ⟨Y.inf ∘ part.right, Y.sup ∘ part.right⟩))
              post)))).IsSuffExplanationAbstract x ε E l) :
    -- and the original, whose exact image `neuronMerging_network_outer` puts inside it
    IsSuffExplanation
      (fun z => fpost (W1 *ᵥ (fun i => σ ((W0 *ᵥ fpre z + b0) i)) + b1)) x ε E l :=
  suffExplanation_of_abstract _ _ x ε E l
    (neuronMerging_network_outer pre post part W0 b0 R W1 b1 Y
      (ofInterval (explainBox x ε E)) hpre hpost hY) hsuffAbs

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
