module

public import CORALean.NN.Instances
public import CORALean.NN.Layers.Operations.Pack
public import CORALean.NN.Operations.ToLayer
public import CORALean.NN.Theorems.NeuronMergingOuter

@[expose] public section

/-!
# A merge at one layer of a whole network

`neuronMerging_sandwich_outer` is stated over the three layers a merge touches. A merge is applied
at a layer *inside* a network, though, and this is that statement: the same sandwich between an
arbitrary prefix and an arbitrary suffix, which is the containment `suffExplanation_of_abstract` [2]
takes as its hypothesis. Neither side is assumed anything of. The prefix contributes only its own
enclosure, so the bounds `Y` are asked for only at the points the prefix reaches; the suffix is
applied to a set on both sides, so the reduction composes with the rest of the network for free, and
merges at two *distant* layers compose by applying this twice. Merges two nonlinear layers apart do
not: they share the linear layer between them.

## Inputs
* `n₀` – input width
* `n₁` – width after the prefix
* `n` – width of the merged layer
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
* `X` – input set
* `fpre` – map of the prefix
* `fpost` – map of the suffix

## Hypotheses
* `hR` – relaxation is sound for the activation
* `hpre` – the prefix encloses its map
* `hpost` – the suffix encloses its map
* `hY` – the bounds contain the activations over the prefix's enclosure

## Conclusion
* the image under the whole network lies in the enclosure of the merged network

## References

* [1] T. Ladner and M. Althoff. "Fully Automatic Neural Network Reduction for Formal Verification".
      Transactions on Machine Learning Research, 2025.
* [2] `CORALean.suffExplanation_of_abstract`.
-/

-- Authors:       Claude Opus 5
-- Written:       06-September-2026
-- Last update:   23-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix ContSet Float Float.SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋]
  {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)] [∀ n, Plus (S n) (Vec ℝ n)]
  [Mtimes (Mat 𝕋) S] [IntervalOuter S 𝕋] [OfInterval S 𝕋]


-- =======================================  MAIN THEOREM  ======================================= --

/-- Neuron merging, [1, Prop. 4], at a layer of any network: the
merged sandwich sits between `pre` and `post`, and `Y` is only ever asked to
bound the nonlinear layer over what `pre` reaches. -/
theorem neuronMerging_network_outer {n₀ n₁ n n₂ n₃ d r : ℕ}
    (pre : NeuralNetwork S n₀ n₁) (post : NeuralNetwork S n₂ n₃)
    (part : Split (Fin n) into (Fin d) ⊕ (Fin r))
    (W0 : Mat 𝕋 n n₁) (b0 : Vec 𝕋 n) {σ : ℝ → ℝ} (R : Relaxation 𝕋) (hR : R.IsSound σ)
    (W1 : Mat 𝕋 n₂ n) (b1 : Vec 𝕋 n₂) (Y : Interval (Vec 𝕋 n)) (X : S n₀)
    {fpre : Vec ℝ n₀ → Vec ℝ n₁} (hpre : pre.Encloses fpre)
    {fpost : Vec ℝ n₂ → Vec ℝ n₃} (hpost : post.Encloses fpost)
    (hY : ∀ x ∈ construct (pre.enclose X),
      (fun i => σ ((toRealMat W0 *ᵥ x + toRealVec b0) i)) ∈ Y.construct) : -- --- CONCL ---
    (fun x => fpost (toRealMat W1 *ᵥ (fun i => σ ((toRealMat W0 *ᵥ fpre x + toRealVec b0) i))
        + toRealVec b1)) '' construct X
      ⊆ construct ((NeuralNetwork.layer (Enclose.pack (S := S) pre)
          (.layer (LinearLayer.mk (W0.submatrix part.left id) (b0 ∘ part.left))
            (.layer (ActivationLayer.of hR)
              (.layer (LinearWithErrorLayer.mk (W1.submatrix id part.left) b1
                  (Interval.mtimes (W1.submatrix id part.right)
                    ⟨Y.inf ∘ part.right, Y.sup ∘ part.right⟩))
                post)))).enclose X) := by -- --- PROOF ---
  rintro _ ⟨x, hx, rfl⟩
  -- the prefix hands the sandwich a set, and that set is what `hY` is stated over
  have hp : fpre x ∈ construct (pre.enclose X) := hpre.enclose_outer X x hx
  have hmid := neuronMerging_sandwich_outer part W0 b0 R hR W1 b1 Y (pre.enclose X) hY
    ⟨fpre x, hp, rfl⟩
  -- the suffix is unchanged, so its own obligation carries the point the rest of the way
  exact hpost.enclose_outer _ _ hmid

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
