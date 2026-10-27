module

public import CORALean.ContSet.Interval.Float.Theorems.MtimesOuter
public import CORALean.Global.Partition
public import CORALean.NN.Layers.Definitions.Enclosure
public import CORALean.NN.Layers.Definitions.Relaxation
public import CORALean.NN.Layers.Operations.Activation
public import CORALean.NN.Layers.Operations.Linear
public import CORALean.NN.Layers.Operations.LinearWithError
public import CORALean.ContSet.Interval.Float.Theorems.SubsetNonemptyHull
public import CORALean.NN.Layers.Instances
public import CORALean.NN.Layers.Operations.ActivationLayerOf
public import CORALean.NN.Layers.Theorems.ActivationEncloses
public import CORALean.NN.Layers.Theorems.LinearEncloses
public import CORALean.NN.Layers.Theorems.LinearWithErrorMem
public import CORALean.NN.NeuralNetwork
public import CORALean.NN.Operations.Basic
public import CORALean.NN.Operations.Enclose

@[expose] public section

/-!
# Neuron merging: sound at every bucket

[1, Prop. 4]. Given output bounds `Y` for a nonlinear layer `k` and *any* split of its neurons into
survivors `B̄` and a bucket `B`, trimming the adjacent linear layers to `B̄` and boxing what `B`
would have contributed to layer `k+1` — `W_{k+1}(·,B) · Y(B)` — soundly encloses the exact sandwich.
The bucket tolerance that picks a *good* `B` never appears: the proof holds at every `B`, which
makes it a heuristic rather than a soundness hypothesis, exactly as `ConPolyZono.reduceBy_outer`
holds at every pair of partitions. It holds at every scalar: the trimming only selects stored
weights, and the box's product rounds outward.

## Inputs
* `n0` – input width
* `n` – width of the merged layer
* `n2` – output width
* `d` – number of surviving neurons
* `r` – number of merged neurons
* `part` – split into survivors and merged neurons
* `W0` – first weight matrix
* `b0` – first bias vector
* `σ` – activation function
* `R` – relaxation of the activation
* `W1` – second weight matrix
* `b1` – second bias vector
* `Y` – bounds of the merged layer
* `X` – input set

## Hypotheses
* `hR` – relaxation is sound for the activation
* `hY` – the bounds contain the activations over the input set

## Conclusion
* the sandwich's image lies in the enclosure of the merged sandwich

## References

* [1] [T. Ladner and M. Althoff. "Fully Automatic Neural Network Reduction for Formal Verification".
      Transactions on Machine Learning Research,
      2025.](../../../../references/2023/ladner-tmlr-network-reduction.md)
-/

-- Authors:       Claude Opus 5
-- Written:       05-September-2026
-- Last update:   23-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix ContSet Float Float.SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋]
  {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)] [∀ n, Plus (S n) (Vec ℝ n)]
  [Mtimes (Mat 𝕋) S] [IntervalOuter S 𝕋] [OfInterval S 𝕋]


-- =======================================  MAIN THEOREM  ======================================= --

/-- Neuron merging, [1, Prop. 4]: sound at *every* bucket
`part.right`, trimming layer `k-1`'s rows and layer `k+1`'s columns to the
survivors `part.left`, and boxing the bucket's contribution to `k+1` from `Y`. -/
theorem neuronMerging_sandwich_outer {n0 n n2 d r : ℕ}
    (part : Split (Fin n) into (Fin d) ⊕ (Fin r))
    (W0 : Mat 𝕋 n n0) (b0 : Vec 𝕋 n) {σ : ℝ → ℝ} (R : Relaxation 𝕋) (hR : R.Encloses σ)
    (W1 : Mat 𝕋 n2 n) (b1 : Vec 𝕋 n2) (Y : Interval (Vec 𝕋 n)) (X : S n0)
    (hY : ∀ x ∈ construct X,
      (fun i => σ ((toRealMat W0 *ᵥ x + toRealVec b0) i)) ∈ Y.construct) : -- --- CONCL ---
    (fun x => toRealMat W1 *ᵥ (fun i => σ ((toRealMat W0 *ᵥ x + toRealVec b0) i))
        + toRealVec b1) '' construct X
      ⊆ construct
        ((NeuralNetwork.layer (LinearLayer.mk (W0.submatrix part.left id) (b0 ∘ part.left))
            (NeuralNetwork.layer (ActivationLayer.of hR)
              (NeuralNetwork.ofLayer (LinearWithErrorLayer.mk (W1.submatrix id part.left) b1
                (Interval.mtimes (W1.submatrix id part.right)
                  ⟨Y.inf ∘ part.right, Y.sup ∘ part.right⟩)))) :
          NeuralNetwork S n0 n2).enclose X) := by -- --- PROOF ---
  rintro _ ⟨x, hx, rfl⟩
  set hk : Vec ℝ n := fun i => σ ((toRealMat W0 *ᵥ x + toRealVec b0) i) with hhk
  -- layer `k-1`, restricted to the survivors: rows commute with row-selection
  have hrow : toRealMat (W0.submatrix part.left id) *ᵥ x + toRealVec (b0 ∘ part.left)
      = (toRealMat W0 *ᵥ x + toRealVec b0) ∘ part.left := by
    funext i
    simp [Matrix.mulVec, dotProduct, toRealMat, toRealVec]
  have hA1 := (Layer.linear_encloses (S := S) (W0.submatrix part.left id)
    (b0 ∘ part.left)).enclose_outer X x hx
  rw [hrow] at hA1
  have hA2 := (Layer.activation_encloses (S := S) hR).enclose_outer _ _ hA1
  -- the bucket's exact output lies in `Y`, hence in `Y` restricted to the bucket
  have hB : hk ∘ part.right
      ∈ (⟨Y.inf ∘ part.right, Y.sup ∘ part.right⟩ : Interval (Vec 𝕋 r)).construct :=
    fun i => hY x hx (part.right i)
  -- the bucket's contribution, which is what the error box of layer `k+1` holds
  set W1' := toRealMat W1
  have hc : toRealVec b1 + W1'.submatrix id part.right *ᵥ (hk ∘ part.right) - toRealVec b1
      ∈ (Interval.mtimes (W1.submatrix id part.right)
          ⟨Y.inf ∘ part.right, Y.sup ∘ part.right⟩).construct := by
    rw [add_sub_cancel_left]
    exact Interval.mtimes_outer (W1.submatrix id part.right) _ ⟨_, hB, rfl⟩
  have hA3 := Layer.linearWithError_mem (S := S) (W1.submatrix id part.left)
    (Interval.construct_subset_nonemptyHull _ hc) _ hA2
  -- layer `k+1`'s dot product splits along the survivors and the bucket
  have hval : W1' *ᵥ hk + toRealVec b1 = W1'.submatrix id part.left *ᵥ (hk ∘ part.left)
      + (toRealVec b1 + W1'.submatrix id part.right *ᵥ (hk ∘ part.right)) := by
    rw [part.mulVec_split₂ W1' hk]
    abel
  show W1' *ᵥ hk + toRealVec b1 ∈ _
  rw [hval]
  exact hA3

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
