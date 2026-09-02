import CORALean.NN.Float.Layers.Linear
import CORALean.NN.Float.Layers.ReLU
import CORALean.NN.Theorems.Robustness

/-!
# The same feed-forward network, over a floating-point scalar

`Examples.FeedForward` at `Float.Zonotope 𝕋` instead of `Real.Zonotope`, and the
point of compiling it is what does *not* appear below: `NeuralNetwork`, `.cons`,
`propagate`, `propagate_outer`, `mem_safeSet` and `classifies` are the exact
layer's, used unchanged. Only the three layer constructors are float ones, and
only because their weights are stored in `𝕋`.

So the network is a `Real.NeuralNetwork` over a float representation, and that
is not a loophole: `Layer` is indexed by a `ContSet` whose ambient type is
`Vec ℝ n`, which is what a float representation denotes through
`InflatedContSet`. What the network encloses is the exact affine map the stored
floats describe, composed with the exact `relu`.

Every operation here computes, unlike the exact version, provided `𝕋` does —
which is the whole reason for the float layer and the sentence the exact
example's docstring ends on.
-/

-- Authors:       Tobias Ladner
-- Written:       02-September-2026
-- Last update:   ---
-- Last revision: ---

namespace CORALean.Float

open ContSet

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋]

/-- Affine, ReLU, affine: two inputs, three hidden neurons, two labels. -/
def Example.feedForward (W₁ : Mat 𝕋 3 2) (b₁ : Vec 𝕋 3) (W₂ : Mat 𝕋 2 3) (b₂ : Vec 𝕋 2) :
    Real.NeuralNetwork (Zonotope 𝕋) 2 2 :=
  .cons (Layer.linear (S := Zonotope 𝕋) W₁ b₁)
    (.cons (Layer.relu) (.cons (Layer.linear W₂ b₂) .nil))

-- Anonymous, since their content is that they elaborate: each is the exact
-- layer's general theorem, read at a float representation.

/-- Every output over the whole input set is in the zonotope that comes back. -/
example (nn : Real.NeuralNetwork (Zonotope 𝕋) 2 2) (X : Zonotope 𝕋 2) {x : Vec ℝ 2}
    (hx : x ∈ construct X) : nn.eval x ∈ construct (nn.propagate X) :=
  nn.propagate_outer X x hx

/-- A safe set the propagated zonotope stays inside is a safe set every output
stays inside. -/
example (nn : Real.NeuralNetwork (Zonotope 𝕋) 2 2) (X : Zonotope 𝕋 2)
    {safe : Set (Vec ℝ 2)} (h : construct (nn.propagate X) ⊆ safe) {x : Vec ℝ 2}
    (hx : x ∈ construct X) : nn.eval x ∈ safe :=
  nn.mem_safeSet X h hx

/-- Robust classification, discharged by the same bound per rival label. -/
example (nn : Real.NeuralNetwork (Zonotope 𝕋) 2 2) (X : Zonotope 𝕋 2) (l : Fin 2)
    (u : ∀ j, SupportBound (construct (nn.propagate X)) (Real.marginDir 2 j l))
    (h : ∀ j, j ≠ l → (u j).val < 0) {x : Vec ℝ 2} (hx : x ∈ construct X)
    {j : Fin 2} (hj : j ≠ l) : nn.eval x j < nn.eval x l :=
  nn.classifies X l u h hx hj

/-- The network above is one of those, which is the only thing left to check. -/
example (W₁ : Mat 𝕋 3 2) (b₁ : Vec 𝕋 3) (W₂ : Mat 𝕋 2 3) (b₂ : Vec 𝕋 2)
    (X : Zonotope 𝕋 2) : Zonotope 𝕋 2 :=
  (Example.feedForward W₁ b₁ W₂ b₂).propagate X

end CORALean.Float
