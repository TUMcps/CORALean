import CORALean.Examples.ConvNet
import CORALean.NN.Float.Layers.Pooling
import CORALean.NN.Float.Layers.ReLU
import CORALean.NN.Float.Layers.Softmax
import CORALean.NN.Theorems.Robustness

/-!
# The same convolutional network, over a floating-point scalar

`Examples.ConvNet` at `Float.Zonotope 𝕋`, and what is worth reading is which
lines changed and which did not.

The taps did not: `Example.convTap` and `Example.poolTap` are the exact layer's,
reused verbatim, because an index function has no scalar in it. That is the
claim `Layers/Convolution` makes about padding, stride and layout, checked here
rather than asserted.

The reshape did not either, and this is the file where that claim is tested:
`Layer.reshape` below is `Real.Layer.reshape`, at a float representation, and it
is sound there for the reason its own docstring gives — a relabelling carries no
weights, so there is nothing to round and no float constructor to write. What
the float layer owes is the `Reindex` instance, and `Zonotope 𝕋` has it.

Batch normalization is the other one with no float file, and it is spelled out
here as what it is: `Float.Layer.linear` at a folded scale and shift, taken as
parameters. The fold — a division by a square root, which `FloatOps` cannot do —
happens once when a network is read, and the layer encloses the affine map the
folded numbers denote, exactly as it encloses the map a stored weight matrix
denotes.

`k` is the exponential's reduction depth in the softmax, and it is precision
alone: every `k` is sound and a larger one tighter.

One honest wrinkle, and it is the bundle's rather than the float layer's:
`noncomputable`. `Layer` carries `eval` alongside `propagate`, max pooling's
`eval` is a supremum over ℝ, and ordering reals is not computable — so the
network below cannot be run even though every step of its `propagate` is float
arithmetic. `Examples.FeedForwardFloat` avoids this only because `relu` and an
affine map are computable over ℝ.
-/

-- Authors:       Tobias Ladner
-- Written:       03-September-2026
-- Last update:   ---
-- Last revision: ---

namespace CORALean.Float

open ContSet SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋]

/-- `W` and `bn` are batch normalization's folded scale and shift, which is all
`BatchNorm` ever was; `k` is the softmax exponential's reduction depth. -/
noncomputable def Example.convNet (k : ℕ) (K : Fin 1 → Fin 2 → 𝕋) (b : Vec 𝕋 5)
    (W : Mat 𝕋 2 2) (bn : Vec 𝕋 2) : Real.NeuralNetwork (Zonotope 𝕋) 6 2 :=
  .cons (Real.Layer.reshape (S := Zonotope 𝕋) (Real.Fin.transposeEquiv 3 2))
    (.cons (Layer.conv (fun _ => 0) Real.Example.convTap K b)
      (.cons (Layer.relu)
        (.cons (Layer.maxPool Real.Example.poolTap fun _ _ => 0)
          (.cons (Layer.linear W bn)
            (.cons (Layer.softmax k) .nil)))))

-- Anonymous, since their content is that they elaborate: each is the exact
-- layer's general theorem, read at a float representation.

/-- The whole chain is a network, which is the only thing left to check. -/
noncomputable example (k : ℕ) (K : Fin 1 → Fin 2 → 𝕋) (b : Vec 𝕋 5) (W : Mat 𝕋 2 2)
    (bn : Vec 𝕋 2) (X : Zonotope 𝕋 6) : Zonotope 𝕋 2 :=
  (Example.convNet k K b W bn).propagate X

/-- Every output over the whole input set is in the zonotope that comes back. -/
example (nn : Real.NeuralNetwork (Zonotope 𝕋) 6 2) (X : Zonotope 𝕋 6) {x : Vec ℝ 6}
    (hx : x ∈ construct X) : nn.eval x ∈ construct (nn.propagate X) :=
  nn.propagate_outer X x hx

/-- Robust classification, discharged by the same bound per rival label. -/
example (nn : Real.NeuralNetwork (Zonotope 𝕋) 6 2) (X : Zonotope 𝕋 6) (l : Fin 2)
    (u : ∀ j, SupportBound (construct (nn.propagate X)) (Real.marginDir 2 j l))
    (h : ∀ j, j ≠ l → (u j).val < 0) {x : Vec ℝ 6} (hx : x ∈ construct X)
    {j : Fin 2} (hj : j ≠ l) : nn.eval x j < nn.eval x l :=
  nn.classifies X l u h hx hj

/-- The stored kernel denotes the convolution exactly, the stencil's entries
being placed rather than summed. -/
example (K : Fin 1 → Fin 2 → 𝕋) (b : Vec 𝕋 5) (x : Vec ℝ 6) (j : Fin 5) :
    (Layer.conv (S := Zonotope 𝕋) (fun _ => 0) Real.Example.convTap K b).eval x j
      = (∑ l, toReal (K 0 l) * x (Real.Example.convTap j l)) + toReal (b j) :=
  Layer.conv_eval _ _ _ _ Real.Example.convTap_injective x j

/-- Exact at a float representation too, which is what having no float
constructor of its own is worth. -/
example (X : Zonotope 𝕋 6) :
    construct ((Real.Layer.reshape (S := Zonotope 𝕋)
        (Real.Fin.transposeEquiv 3 2)).propagate X)
      = (Real.Layer.reshape (S := Zonotope 𝕋)
        (Real.Fin.transposeEquiv 3 2)).eval '' construct X :=
  Real.Layer.reshape_exact _ X

/-- Average pooling takes its reciprocal as data, `1 / k` being no float; for a
window of two it is `half one`, which is exact. -/
def Example.avgPoolTwo : Real.Layer (Zonotope 𝕋) 5 2 :=
  Layer.avgPool (FloatOps.half FloatOps.one) Real.Example.poolTap

end CORALean.Float
