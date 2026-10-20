import CORALean.Global.Float.Instances.Real.Theorems.Basic
import CORALean.NN.Definitions.Reduction
import CORALean.NN.Definitions.Encloses
import CORALean.NN.Layers.Definitions.Relu
import CORALean.NN.Layers.Operations.Activation
import CORALean.NN.Layers.Operations.Conv
import CORALean.NN.Layers.Operations.Linear
import CORALean.NN.Layers.Operations.LinearWithError
import CORALean.NN.Layers.Operations.Basic
import CORALean.NN.Layers.Operations.ReluRelaxation
import CORALean.NN.Layers.Operations.ReluSlope
import CORALean.NN.Layers.Operations.TapMat
import CORALean.NN.Layers.Theorems.ActivationLayerOfEncloses
import CORALean.NN.Layers.Theorems.ConvEncloses
import CORALean.NN.Layers.Theorems.LinearEncloses
import CORALean.NN.Layers.Theorems.ReluRelaxationSound
import CORALean.NN.Layers.Theorems.ReluEncloses
import CORALean.NN.Layers.Theorems.TapMatMulVec
import CORALean.NN.Theorems.ReducesAtOuter
import CORALean.ContSet.Conversion.Float.Operations.Basic
import CORALean.ContSet.Conversion.Float.Operations.PolyZonotope_to_Interval
import CORALean.ContSet.Conversion.Float.Operations.Zonotope_to_Interval
import CORALean.ContSet.Conversion.Real.Operations.Basic
import CORALean.ContSet.Conversion.Real.Operations.PolyZonotope_to_Interval
import CORALean.ContSet.Conversion.Real.Operations.Zonotope_to_Interval

/-!
# Sound compression by an identity convolution, and [1, Cor. 1]

`Cor. 1`'s network: two convolutional layers at the identity-like kernel `K(k,l,1,1) = δ_{kl}`,
sandwiching one ReLU, applied to a nonnegative "uncertain image" `X`. A convolution is
`Layer.linear` at its stencil matrix, and the network is written with that matrix, `compressW`, as
`LinearLayer`s, the form `ReducesAt.merge` matches. The corollary needs nothing beyond `Thm. 1`
applied at this one network: the two convolutions compute the identity, so on a nonnegative image
the ReLU between them is the identity too, and `reducesAt_outer` puts `X` inside whatever network
`ReducesAt.merge` reduces this one to, at any split of its hidden layer; the split chosen here is
one instance of "dynamic merge buckets".

## Inputs
* none

## Output
* compression network of two convolutions and a ReLU

## References

* [1] T. Ladner and M. Althoff. "Fully Automatic Neural Network Reduction for
      Formal Verification". TMLR. arXiv:2305.01932.
-/

-- Authors:       Claude Opus 5
-- Written:       12-September-2026
-- Last update:   23-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix ContSet Plus Mtimes IntervalOuter OfInterval

/-- The single tap output `j` reads: itself. `K(k,l,1,1) = δ_{kl}` becomes this
once `l = k` is chosen by the tap instead of summed over. -/
def Example.compressTap (j : Fin 3) (_ : Fin 1) : Fin 3 := j

theorem Example.compressTap_injective (j : Fin 3) :
    Function.Injective (Example.compressTap j) := fun a b _ =>
  Fin.ext (by have := a.isLt; have := b.isLt; omega)

/-- Weight `1` on the tap that survives the reindexing above. -/
def Example.compressK : Fin 3 → Fin 1 → ℝ := fun _ _ => 1

/-- The matrix both convolutions share, which `compressW_apply` shows is the
identity. -/
noncomputable def Example.compressW : Mat ℝ 3 3 :=
  tapMat Example.compressTap Example.compressK

theorem Example.compressW_apply (v : Vec ℝ 3) :
    Example.compressW *ᵥ v = v := by -- --- PROOF ---
  funext j
  have h := tapMat_mulVec Example.compressTap Example.compressK
    Example.compressTap_injective v j
  rw [Float.toRealMat_real] at h
  show (tapMat Example.compressTap Example.compressK *ᵥ v) j = v j
  rw [h, Fin.sum_univ_one]
  show (1 : ℝ) * v j = v j
  ring

/-- One kept neuron, two merged: a split of the hidden layer, chosen the way
"dynamic merge buckets" would choose one, but arbitrary otherwise. -/
noncomputable def Example.compressPart : Split (Fin 3) into (Fin 1) ⊕ (Fin 2) :=
  Partition.split 1 2


-- =====================================  MAIN DEFINITION  ====================================== --

/-- [1, Cor. 1]'s compression network: two convolutional layers at the
identity kernel, sandwiching one ReLU. -/
noncomputable def Example.compressNetwork : NeuralNetwork 𝒵 3 3 :=
  .layer (LinearLayer.mk Example.compressW 0)
    (.layer (ActivationLayer.of (n := 3) (reluRelaxation_sound (𝕋 := ℝ) reluSlope))
      (.ofLayer (LinearLayer.mk Example.compressW 0)))

/-- The kernel computes the identity on both sides, so the whole network
computes `relu` alone. -/
theorem Example.compressNetwork_encloses :
    Example.compressNetwork.Encloses (fun x i => Real.relu (x i)) := by -- --- PROOF ---
  -- each convolution is its stencil matrix, a single tap of weight `1`, i.e. `id`
  have hconv : (Enclose.toLayer (S := 𝒵) (LinearLayer.mk Example.compressW
      (0 : Vec ℝ 3))).Encloses (id : Vec ℝ 3 → Vec ℝ 3) :=
    (Layer.linear_encloses Example.compressW 0).congr fun x => by
      show x = Float.toRealMat Example.compressW *ᵥ x + Float.toRealVec (0 : Vec ℝ 3)
      rw [Float.toRealMat_real]
      show x = Example.compressW *ᵥ x + 0
      rw [add_zero, Example.compressW_apply]
  have hrelu := ActivationLayer.of_encloses (S := 𝒵) (n := 3)
    (reluRelaxation_sound (𝕋 := ℝ) reluSlope)
  -- composing `id ∘ relu ∘ id` and simplifying the two identities away
  exact .layer hconv (.layer hrelu (.layer hconv (.output fun _ => rfl) fun _ => rfl)
    fun _ => rfl) fun _ => rfl

/-- [1, Cor. 1] (Sound Compression): reducing the compression network at any
split of its hidden layer keeps every point of a nonnegative "uncertain image"
`X` inside the reduced network's enclosure. -/
theorem Example.exists_compressed_network_contains (X : 𝒵 3)
    (hX : ∀ x ∈ construct X, ∀ i, 0 ≤ x i) :
    ∃ nn' : NeuralNetwork 𝒵 3 3, construct X ⊆ construct (nn'.enclose X) := by -- --- PROOF ---
  -- the identity's output on `X` is `X` itself, so its interval box bounds it
  have hY : ∀ x ∈ construct X, (fun i => Real.relu ((Example.compressW *ᵥ x + 0) i))
      ∈ construct (Float.IntervalOuter.interval (S := 𝒵) X) := by
    intro x hx
    have hzero : Example.compressW *ᵥ x + 0 = x := by
      rw [add_zero]; exact Example.compressW_apply x
    have hid : (fun i => Real.relu ((Example.compressW *ᵥ x + 0) i)) = x := by
      rw [hzero]; funext i; exact max_eq_left (hX x hx i)
    rw [hid]
    exact Float.IntervalOuter.interval_outer (S := 𝒵) X hx
  -- [1, Thm. 1]'s own machinery: `compressNetwork` reduces at the split above
  have hred : NeuralNetwork.ReducesAt X Example.compressNetwork
      (.layer (LinearLayer.mk (Example.compressW.submatrix Example.compressPart.left id)
          ((0 : Vec ℝ 3) ∘ Example.compressPart.left))
        (.layer (ActivationLayer.of (reluRelaxation_sound (𝕋 := ℝ) reluSlope))
          (.ofLayer (LinearWithErrorLayer.mk
            (Example.compressW.submatrix id Example.compressPart.left) (0 : Vec ℝ 3)
            (Float.Interval.mtimes (Example.compressW.submatrix id Example.compressPart.right)
              ⟨(Float.IntervalOuter.interval (S := 𝒵) X).inf ∘ Example.compressPart.right,
                (Float.IntervalOuter.interval (S := 𝒵) X).sup ∘ Example.compressPart.right⟩)))))
      (fun x i => Real.relu (x i)) := by
    unfold Example.compressNetwork NeuralNetwork.ofLayer
    exact NeuralNetwork.ReducesAt.merge (S := 𝒵) X Example.compressPart Example.compressW 0
      (reluRelaxation reluSlope) (reluRelaxation_sound reluSlope)
      Example.compressW 0 (Float.IntervalOuter.interval (S := 𝒵) X) hY
      (h := id) (hf := fun x => by
        -- the identity matrix twice over, wrapping the elementwise `relu`
        have h1 : Example.compressW *ᵥ x + 0 = x := by
          rw [add_zero]; exact Example.compressW_apply x
        have h2 : Example.compressW *ᵥ (fun i => Real.relu (x i)) + 0
            = fun i => Real.relu (x i) := by
          rw [add_zero]; exact Example.compressW_apply _
        show (fun i => Real.relu (x i)) = id
          (Example.compressW *ᵥ (fun i => Real.relu ((Example.compressW *ᵥ x + 0) i)) + 0)
        rw [h1, h2]
        rfl)
      (NeuralNetwork.ReducesAt.nil _ fun _ => rfl)
  -- `X` is `compressNetwork`'s exact image of itself, so the containment lands on `X`
  have hout := NeuralNetwork.reducesAt_outer hred
  exact ⟨_, fun x hx => by
    have hxeq : x = (fun i => Real.relu (x i)) :=
      funext fun i => (max_eq_left (hX x hx i)).symm
    rw [hxeq]
    exact hout ⟨x, hx, rfl⟩⟩

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
