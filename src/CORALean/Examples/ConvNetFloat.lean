import CORALean.Examples.ConvNet
import CORALean.NN.Layers.Definitions.Enclosure
import CORALean.NN.Layers.Definitions.PolyRelaxation
import CORALean.NN.Layers.Definitions.Relaxation
import CORALean.NN.Layers.Definitions.Relu
import CORALean.NN.Layers.Definitions.ScaleRounding
import CORALean.NN.Layers.Definitions.Softmax
import CORALean.NN.Layers.Instances
import CORALean.NN.Layers.Operations.AvgPool
import CORALean.NN.Layers.Operations.BatchNorm
import CORALean.NN.Layers.Operations.Conv
import CORALean.NN.Layers.Operations.MaxPool
import CORALean.NN.Layers.Operations.Basic
import CORALean.NN.Layers.Operations.ReluSlope
import CORALean.NN.Layers.Operations.Reshape
import CORALean.NN.Layers.Operations.Softmax
import CORALean.NN.Layers.Operations.TransposeEquiv
import CORALean.NN.Layers.Theorems.ConvSound
import CORALean.NN.Layers.Theorems.MaxPoolSound
import CORALean.NN.Layers.Theorems.ReshapeExact
import CORALean.NN.Theorems.Classifies
import CORALean.NN.Theorems.EncloseOuter
import CORALean.NN.Operations.MarginDir

/-!
# The same convolutional network, over a floating-point scalar

`Examples.ConvNet` at `Float.Zonotope (Vec 𝕋 n)`, and what is worth reading is which
lines changed and which did not. The taps did not: `Example.convTap` and
`Example.poolTap` are the exact layer's, reused verbatim, because an index
function has no scalar in it.

The layers did not either: each is written once over the scalar, and this is it at
`𝕋`. The reshape carries no scalar at all, sound here because `Zonotope (Vec 𝕋 n)` has the
`Reindex` instance it owes; batch normalization takes its scale and shift folded,
in the scalar, as the network read in stores them.

`Layer` no longer carries what a layer computes, so nothing here stores a real
function: the network below is a plain `def` and every step of its `enclose` is
float arithmetic. Max pooling's supremum over ℝ lives in `Layer.maxPool_sound`,
which is a `Prop`.
-/

-- Authors:       Claude Opus 5
-- Written:       03-September-2026
-- Last update:   23-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open ContSet SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋]

/-- `sc` and `sh` are batch normalization's folded scale and shift, which is all
`BatchNorm` ever was; `k` is the softmax exponential's reduction depth. -/
def Example.convNet (k : ℕ) (K : Fin 1 → Fin 2 → 𝕋) (b : Vec 𝕋 5)
    (sc sh : Vec 𝕋 2) : NeuralNetwork 𝒵[𝕋] 6 2 :=
  .layer (ReshapeLayer.mk (Fin.transposeEquiv 3 2))
    (.layer (ConvLayer.mk 1 2 (fun _ => 0) Real.Example.convTap K b
        Real.Example.convTap_injective)
      (.layer (ReluLayer.mk (𝕋 := 𝕋) reluSlope rfl)
        (.layer (MaxPoolLayer.mk (𝕋 := 𝕋) 1 Real.Example.poolTap fun _ _ => 0)
          (.layer (BatchNormLayer.mk 2 id sc sh rfl)
            (.layer (SoftmaxLayer.mk (𝕋 := 𝕋) k rfl) .output)))))

-- anonymous: each is the exact layer's theorem, read at a float representation

/-- The whole chain is a network, which is the only thing left to check. -/
example (k : ℕ) (K : Fin 1 → Fin 2 → 𝕋) (b : Vec 𝕋 5) (sc sh : Vec 𝕋 2)
    (X : Zonotope (Vec 𝕋 6)) : Zonotope (Vec 𝕋 2) :=
  (Example.convNet k K b sc sh).enclose X

/-- Every output over the whole input set is in the zonotope that comes back. -/
example {nn : NeuralNetwork 𝒵[𝕋] 6 2} {f : Vec ℝ 6 → Vec ℝ 2}
    (hf : nn.Sound f) (X : Zonotope (Vec 𝕋 6)) {x : Vec ℝ 6}
    (hx : x ∈ construct X) : f x ∈ construct (nn.enclose X) :=
  hf.enclose_outer X x hx

/-- Robust classification, discharged by the same bound per rival label. -/
example {nn : NeuralNetwork 𝒵[𝕋] 6 2} {f : Vec ℝ 6 → Vec ℝ 2}
    (hf : nn.Sound f) (X : Zonotope (Vec 𝕋 6)) (l : Fin 2)
    (u : ∀ j, SupportBound (construct (nn.enclose X)) (marginDir 2 j l))
    (h : ∀ j, j ≠ l → (u j).val < 0) {x : Vec ℝ 6} (hx : x ∈ construct X)
    {j : Fin 2} (hj : j ≠ l) : f x j < f x l :=
  NeuralNetwork.classifies hf X l u h hx hj

/-- The stored kernel denotes the convolution exactly, the stencil's entries
being placed rather than summed. -/
example (K : Fin 1 → Fin 2 → 𝕋) (b : Vec 𝕋 5) :
    (Layer.conv (S := 𝒵[𝕋]) (fun _ => 0) Real.Example.convTap K b).Sound
      fun x j => (∑ l, toReal (K 0 l) * x (Real.Example.convTap j l)) + toReal (b j) :=
  Layer.conv_sound _ _ _ _ Real.Example.convTap_injective

/-- Exact at a float representation too, a relabelling carrying no scalar. -/
example (X : Zonotope (Vec 𝕋 6)) :
    construct ((Layer.reshape (S := 𝒵[𝕋])
    (Fin.transposeEquiv 3 2)).enclose X)
      = CORALean.reindexLin (Fin.transposeEquiv 3 2) '' construct X :=
  Layer.reshape_exact (S := 𝒵[𝕋]) _ X


-- =====================================  MAIN DEFINITION  ====================================== --

/-- Average pooling takes its reciprocal as data, `1 / k` being no float; for a
window of two it is `half one`, which is exact. -/
def Example.avgPoolTwo : Layer 𝒵[𝕋] 5 2 :=
  Layer.avgPool (FloatOps.half FloatOps.one) Real.Example.poolTap

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
