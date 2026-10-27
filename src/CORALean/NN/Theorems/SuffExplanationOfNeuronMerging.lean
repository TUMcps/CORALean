module

public import CORALean.NN.Theorems.NeuronMergingNetworkOuter
public import CORALean.NN.Theorems.SuffExplanationTransfer

@[expose] public section

/-!
# Transfer at a network the abstraction actually produces

Split out of `SuffExplanationTransfer.lean` (issue #62): one of the two
corollaries the refinement loop [1, Alg. 2] actually visits, alongside
`SuffExplanationOfEnclose.lean` — merging the bucket `part.right` at one
layer, `hcontain` is `neuronMerging_network_outer` [2] and nothing further is
assumed. The network's weights are in any scalar, the explanation's box real.

## Inputs
* `n₀` – input width
* `n₁` – width after the prefix
* `nk` – width of the merged layer
* `n₂` – width after the second linear layer
* `n₃` – output width
* `d` – number of surviving neurons
* `r` – number of merged neurons
* `pre` – network before the sandwich
* `post` – network after the sandwich
* `part` – split into survivors and merged neurons
* `W0` – first weight matrix
* `b0` – first bias vector
* `σ` – activation function
* `R` – relaxation of the activation
* `W1` – second weight matrix
* `b1` – second bias vector
* `Y` – bounds of the merged layer
* `x` – input point
* `ε` – perturbation radius
* `E` – explanation, a feature set
* `l` – target label
* `fpre` – map of the prefix
* `fpost` – map of the suffix

## Hypotheses
* `hR` – relaxation is sound for the activation
* `hpre` – the prefix encloses its map
* `hpost` – the suffix encloses its map
* `hY` – the bounds contain the activations over the prefix's enclosure
* `hsuffAbs` – the explanation is abstractly sufficient for the merged network

## Conclusion
* the explanation is sufficient for the original composite map

## References

* [1] [S. Bassan, Y. Y. Elboher, T. Ladner, M. Althoff and G. Katz. "Explaining, Fast and Slow:
      Abstraction and Refinement of Provable Explanations". Proceedings of the 42nd International
      Conference on Machine Learning,
      2025.](../../../../references/2025/bassan-icml-explaining-fast-and-slow.md)
* [2] `CORALean.neuronMerging_network_outer`.
-/

-- Authors:       Claude Opus 5
-- Written:       06-September-2026
-- Last update:   23-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix ContSet Real.OfInterval
open Float (toRealMat toRealVec)

variable {𝕋 : Type} [Float.FloatOps 𝕋] [Float.SoundFloatArithmetic 𝕋]
  {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)] [Real.OfInterval S] {n m : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem NeuralNetwork.suffExplanation_of_neuronMerging [∀ n, Plus (S n) (Vec ℝ n)]
    [Mtimes (Mat 𝕋) S] [Float.IntervalOuter S 𝕋] [Float.OfInterval S 𝕋] {n₀ n₁ nk n₂ n₃ d r : ℕ}
    (pre : NeuralNetwork S n₀ n₁) (post : NeuralNetwork S n₂ n₃)
    (part : Split (Fin nk) into (Fin d) ⊕ (Fin r))
    (W0 : Mat 𝕋 nk n₁) (b0 : Vec 𝕋 nk) {σ : ℝ → ℝ} (R : Relaxation 𝕋) (hR : R.IsSound σ)
    (W1 : Mat 𝕋 n₂ nk) (b1 : Vec 𝕋 n₂) (Y : Float.Interval (Vec 𝕋 nk))
    (x : Vec ℝ n₀) (ε : ℝ) (E : Finset (Fin n₀)) (l : Fin n₃)
    {fpre : Vec ℝ n₀ → Vec ℝ n₁} (hpre : pre.Encloses fpre)
    {fpost : Vec ℝ n₂ → Vec ℝ n₃} (hpost : post.Encloses fpost)
    (hY : ∀ z ∈ construct (pre.enclose (ofInterval (explainBox x ε E))),
      (fun i => σ ((toRealMat W0 *ᵥ z + toRealVec b0) i)) ∈ Y.construct)
    -- the reduced network: both linear layers trimmed to `part.left`, the bucket boxed into `k+1`
    (hsuffAbs : (NeuralNetwork.layer (Enclose.pack (S := S) pre)
        (.layer (LinearLayer.mk (W0.submatrix part.left id) (b0 ∘ part.left))
          (.layer (ActivationLayer.of hR)
            (.layer (LinearWithErrorLayer.mk (W1.submatrix id part.left) b1
                (Float.Interval.mtimes (W1.submatrix id part.right)
                  ⟨Y.inf ∘ part.right, Y.sup ∘ part.right⟩))
              post)))).IsSuffExplanationAbstract x ε E l) :
    -- and the original, whose exact image `neuronMerging_network_outer` puts inside it
    IsSuffExplanation
      (fun z => fpost (toRealMat W1 *ᵥ (fun i => σ ((toRealMat W0 *ᵥ fpre z + toRealVec b0) i))
        + toRealVec b1)) x ε E l :=
  suffExplanation_of_abstract _ _ x ε E l
    (neuronMerging_network_outer pre post part W0 b0 R hR W1 b1 Y
      (ofInterval (explainBox x ε E)) hpre hpost hY) hsuffAbs

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
