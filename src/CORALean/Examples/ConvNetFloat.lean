import CORALean.Examples.ConvNet
import CORALean.NN.Float.Layers.Pooling
import CORALean.NN.Float.Layers.ReLU
import CORALean.NN.Float.Layers.Softmax
import CORALean.NN.Theorems.Classifies
import CORALean.NN.Theorems.MarginDir
import CORALean.NN.Theorems.EncloseOuter

/-!
# The same convolutional network, over a floating-point scalar

`Examples.ConvNet` at `Float.Zonotope 𝕋`, and what is worth reading is which
lines changed and which did not. The taps did not: `Example.convTap` and
`Example.poolTap` are the exact layer's, reused verbatim, because an index
function has no scalar in it.

The reshape did not either: `Layer.reshape` below is `Real.Layer.reshape` at a
float representation, sound there because a relabelling carries no weights, and
`Zonotope 𝕋` has the `Reindex` instance it owes.

Batch normalization is the other with no float file, spelled out here as
`Float.Layer.linear` at a folded scale and shift taken as parameters.

`Layer` no longer carries what a layer computes, so nothing here stores a real
function: the network below is a plain `def` and every step of its `enclose` is
float arithmetic. Max pooling's supremum over ℝ lives in `Layer.maxPool_sound`,
which is a `Prop`.
-/

-- Authors:       Tobias Ladner
-- Written:       03-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open ContSet SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋]

/-- `W` and `bn` are batch normalization's folded scale and shift, which is all
`BatchNorm` ever was; `k` is the softmax exponential's reduction depth. -/
def Example.convNet (k : ℕ) (K : Fin 1 → Fin 2 → 𝕋) (b : Vec 𝕋 5)
    (W : Mat 𝕋 2 2) (bn : Vec 𝕋 2) : NeuralNetwork (Zonotope 𝕋) 6 2 :=
  .cons (Real.Layer.reshape (S := Zonotope 𝕋) (Real.Fin.transposeEquiv 3 2))
    (.cons (Layer.conv (fun _ => 0) Real.Example.convTap K b)
      (.cons (Layer.relu)
        (.cons (Layer.maxPool Real.Example.poolTap fun _ _ => 0)
          (.cons (Layer.linear W bn)
            (.cons (Layer.softmax k) .nil)))))

-- anonymous: each is the exact layer's theorem, read at a float representation

/-- The whole chain is a network, which is the only thing left to check. -/
example (k : ℕ) (K : Fin 1 → Fin 2 → 𝕋) (b : Vec 𝕋 5) (W : Mat 𝕋 2 2)
    (bn : Vec 𝕋 2) (X : Zonotope 𝕋 6) : Zonotope 𝕋 2 :=
  (Example.convNet k K b W bn).enclose X

/-- Every output over the whole input set is in the zonotope that comes back. -/
example {nn : NeuralNetwork (Zonotope 𝕋) 6 2} {f : Vec ℝ 6 → Vec ℝ 2}
    (hf : nn.Sound f) (X : Zonotope 𝕋 6) {x : Vec ℝ 6}
    (hx : x ∈ construct X) : f x ∈ construct (nn.enclose X) :=
  hf.enclose_outer X x hx

/-- Robust classification, discharged by the same bound per rival label. -/
example {nn : NeuralNetwork (Zonotope 𝕋) 6 2} {f : Vec ℝ 6 → Vec ℝ 2}
    (hf : nn.Sound f) (X : Zonotope 𝕋 6) (l : Fin 2)
    (u : ∀ j, SupportBound (construct (nn.enclose X)) (marginDir 2 j l))
    (h : ∀ j, j ≠ l → (u j).val < 0) {x : Vec ℝ 6} (hx : x ∈ construct X)
    {j : Fin 2} (hj : j ≠ l) : f x j < f x l :=
  NeuralNetwork.classifies hf X l u h hx hj

/-- The stored kernel denotes the convolution exactly, the stencil's entries
being placed rather than summed. -/
example (K : Fin 1 → Fin 2 → 𝕋) (b : Vec 𝕋 5) :
    (Layer.conv (S := Zonotope 𝕋) (fun _ => 0) Real.Example.convTap K b).Sound
      fun x j => (∑ l, toReal (K 0 l) * x (Real.Example.convTap j l)) + toReal (b j) :=
  Layer.conv_sound _ _ _ _ Real.Example.convTap_injective

/-- Exact at a float representation too, which is what having no float
constructor of its own is worth. -/
example (X : Zonotope 𝕋 6) :
    construct ((Real.Layer.reshape (S := Zonotope 𝕋)
        (Real.Fin.transposeEquiv 3 2)).enclose X)
      = CORALean.reindexLin (Real.Fin.transposeEquiv 3 2) '' construct X :=
  Real.Layer.reshape_exact _ X


-- =====================================  MAIN DEFINITION  ====================================== --

/-- Average pooling takes its reciprocal as data, `1 / k` being no float; for a
window of two it is `half one`, which is exact. -/
def Example.avgPoolTwo : Layer (Zonotope 𝕋) 5 2 :=
  Layer.avgPool (FloatOps.half FloatOps.one) Real.Example.poolTap

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
