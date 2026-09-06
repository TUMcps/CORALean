import CORALean.ContSet.Conversion.Real.API
import CORALean.NN.Layers.BatchNorm
import CORALean.NN.Layers.Pooling
import CORALean.NN.Layers.ReLU
import CORALean.NN.Layers.Reshape
import CORALean.NN.Layers.Softmax
import CORALean.NN.Theorems.Classifies
import CORALean.NN.Theorems.MarginDir
import CORALean.NN.Theorems.PropagateOuter

/-!
# A convolutional network, and the six layers it puts in one chain

`Examples.FeedForward` at the rest of `Layers/`: reshape, convolution, ReLU, max
pooling, batch normalization and softmax, chained at `Zonotope` with nothing
supplied but the instances that representation already had. Compiled, so a layer
whose instances stop resolving fails the build here.

What the chain shows is that the layers' *interfaces* compose, and unevenly: the
reshape asks for `Reindex` alone, the softmax for the two box conversions alone,
and the four in between for `Mtimes` and `Plus` as well.

The two `_eval` checks below are the other half. A layer's soundness field says
nothing about *which* function was enclosed, so a convolution defined as
`Layer.linear` at a stencil is only a convolution because `conv_eval` says the
stencil computes one. `reshape_exact` is the opposite case, the only equality in
`NN`. The taps are written out rather than generated, since what is checked is
that the index function is *all* a convolution needs to say about padding, stride
and layout.
-/

-- Authors:       Tobias Ladner
-- Written:       03-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open ContSet

/-- Width-two windows over six inputs, sliding by one: output `j` reads `j` and
`j + 1`. -/
def Example.convTap (j : Fin 5) (l : Fin 2) : Fin 6 :=
  ⟨j.val + l.val, by have hj := j.isLt; have hl := l.isLt; omega⟩

/-- Width-two windows over five inputs, sliding by two, which is what a pooling
window is: output `j` reads `2 j` and `2 j + 1`. -/
def Example.poolTap (j : Fin 2) (l : Fin 2) : Fin 5 :=
  ⟨2 * j.val + l.val, by have hj := j.isLt; have hl := l.isLt; omega⟩

theorem Example.convTap_injective (j : Fin 5) : Function.Injective (Example.convTap j) :=
  fun _ _ h => Fin.ext (Nat.add_left_cancel (congrArg Fin.val h))


-- =====================================  MAIN DEFINITION  ====================================== --

/-- A 2 × 3 array read the other way round, then convolved, rectified, pooled,
normalized and turned into two class scores. -/
noncomputable def Example.convNet (K : Fin 1 → Fin 2 → ℝ) (b : Vec ℝ 5)
    (gamma beta mean var : Vec ℝ 2) : NeuralNetwork 𝒵 6 2 :=
  .cons (Layer.reshape (S := 𝒵) (Fin.transposeEquiv 3 2))
    (.cons (Layer.conv (fun _ => 0) Example.convTap K b)
      (.cons Layer.relu
        (.cons (Layer.maxPool Example.poolTap fun _ _ => 0)
          (.cons (Layer.batchNorm id gamma beta mean var 1e-5)
            (.cons Layer.softmax .nil)))))

-- anonymous, since their content is that they elaborate at this network

/-- The whole chain is a network, which is the only thing left to check. -/
noncomputable example (K : Fin 1 → Fin 2 → ℝ) (b : Vec ℝ 5)
    (gamma beta mean var : Vec ℝ 2) (X : Zonotope (Vec ℝ 6)) : Zonotope (Vec ℝ 2) :=
  (Example.convNet K b gamma beta mean var).propagate X

/-- Every output over the whole input set is in the zonotope that comes back. -/
example (nn : NeuralNetwork 𝒵 6 2) (X : Zonotope (Vec ℝ 6)) {x : Vec ℝ 6}
    (hx : x ∈ construct X) : nn.eval x ∈ construct (nn.propagate X) :=
  nn.propagate_outer X x hx

/-- Robust classification at two labels, unchanged by the layers in between. -/
example (nn : NeuralNetwork 𝒵 6 2) (X : Zonotope (Vec ℝ 6)) (l : Fin 2)
    (u : ∀ j, SupportBound (construct (nn.propagate X)) (marginDir 2 j l))
    (h : ∀ j, j ≠ l → (u j).val < 0) {x : Vec ℝ 6} (hx : x ∈ construct X)
    {j : Fin 2} (hj : j ≠ l) : nn.eval x j < nn.eval x l :=
  nn.classifies X l u h hx hj

/-- The stencil computes the convolution, which is what makes the linear layer
under it one. -/
example (K : Fin 1 → Fin 2 → ℝ) (b : Vec ℝ 5) (x : Vec ℝ 6) (j : Fin 5) :
    (Layer.conv (S := 𝒵) (fun _ => 0) Example.convTap K b).eval x j
      = (∑ l, K 0 l * x (Example.convTap j l)) + b j :=
  Layer.conv_eval _ _ _ _ Example.convTap_injective x j

/-- The reshape loses nothing, and no hypothesis is needed to say so. -/
example (X : Zonotope (Vec ℝ 6)) :
    construct ((Layer.reshape (S := 𝒵) (Fin.transposeEquiv 3 2)).propagate X)
      = (Layer.reshape (S := 𝒵) (Fin.transposeEquiv 3 2)).eval '' construct X :=
  Layer.reshape_exact (S := 𝒵) _ X

/-- Average pooling is not in the chain above because it is the convolution
already there at a constant kernel; it is checked separately for the same
reason. -/
noncomputable example : Layer 𝒵 5 2 := Layer.avgPool Example.poolTap

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
