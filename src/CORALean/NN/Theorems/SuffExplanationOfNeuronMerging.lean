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

## References

* [1] S. Bassan, Y. Y. Elboher, T. Ladner, M. Althoff and G. Katz. "Explaining
      Fast and Slow: Abstraction and Refinement of Provable Explanations".
      ICML 2025.
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
    (W0 : Mat 𝕋 nk n₁) (b0 : Vec 𝕋 nk) {σ : ℝ → ℝ} (R : Relaxation 𝕋) (hR : R.Sound σ)
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
              post)))).IsSuffExplanationAbstract x ε E l) : -- --- CONCL ---
    -- and the original, whose exact image `neuronMerging_network_outer` puts inside it
    IsSuffExplanation
      (fun z => fpost (toRealMat W1 *ᵥ (fun i => σ ((toRealMat W0 *ᵥ fpre z + toRealVec b0) i))
        + toRealVec b1)) x ε E l :=
  suffExplanation_of_abstract _ _ x ε E l
    (neuronMerging_network_outer pre post part W0 b0 R hR W1 b1 Y
      (ofInterval (explainBox x ε E)) hpre hpost hY) hsuffAbs

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
