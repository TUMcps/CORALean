import CORALean.NN.Float.Layers.Linear
import CORALean.NN.Float.Layers.ReLU
import CORALean.NN.Float.Layers.SigmoidPoly
import CORALean.NN.Float.Layers.Tanh
import CORALean.NN.Theorems.Classifies
import CORALean.NN.Theorems.MarginDir
import CORALean.NN.Theorems.MemSafeSet
import CORALean.NN.Theorems.EncloseOuter

/-!
# The same feed-forward network, over a floating-point scalar

`Examples.FeedForward` at `Float.Zonotope 𝕋` instead of `Real.Zonotope`, and the
point of compiling it is what does *not* appear below: `NeuralNetwork`, `.cons`,
`enclose`, `enclose_outer`, `mem_safeSet` and `classifies` are the exact layer's,
used unchanged. Only the layer constructors are float ones, their weights in `𝕋`.

So the network is a `NeuralNetwork` over a float representation, and that
is not a loophole: `Layer` is indexed by a `ContSet` whose ambient type is
`Vec ℝ n`, which is what a float representation denotes through
`InflatedContSet`. What the network encloses is the exact affine map the stored
floats describe, composed with the exact `relu`.

Every operation here computes, unlike the exact version, provided `𝕋` does —
which is the whole reason for the float layer. `sigmoidTanhNet` is the same
point where it used to fail: `Layer` stores no function, so a chain holding
sigmoid and tanh is a plain `def`. `sigmoidPolyNet` is the last chain to join
them, its relaxation storing floats and naming `Real.sigmoid` only in a proof.
-/

-- Authors:       Tobias Ladner
-- Written:       02-September-2026
-- Last update:   07-September-2026
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open scoped Matrix
open ContSet

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- Affine, ReLU, affine: two inputs, three hidden neurons, two labels. -/
def Example.feedForward (W₁ : Mat 𝕋 3 2) (b₁ : Vec 𝕋 3) (W₂ : Mat 𝕋 2 3) (b₂ : Vec 𝕋 2) :
    NeuralNetwork (Zonotope 𝕋) 2 2 :=
  .cons (Layer.linear (S := Zonotope 𝕋) W₁ b₁)
    (.cons (Layer.relu) (.cons (Layer.linear W₂ b₂) .nil))

-- anonymous: each is the exact layer's theorem, read at a float representation

/-- Every output over the whole input set is in the zonotope that comes back. -/
example {nn : NeuralNetwork (Zonotope 𝕋) 2 2} {f : Vec ℝ 2 → Vec ℝ 2}
    (hf : nn.Sound f) (X : Zonotope 𝕋 2) {x : Vec ℝ 2}
    (hx : x ∈ construct X) : f x ∈ construct (nn.enclose X) :=
  hf.enclose_outer X x hx

/-- A safe set the enclosed zonotope stays inside is a safe set every output
stays inside. -/
example {nn : NeuralNetwork (Zonotope 𝕋) 2 2} {f : Vec ℝ 2 → Vec ℝ 2}
    (hf : nn.Sound f) (X : Zonotope 𝕋 2)
    {safe : Set (Vec ℝ 2)} (h : construct (nn.enclose X) ⊆ safe) {x : Vec ℝ 2}
    (hx : x ∈ construct X) : f x ∈ safe :=
  NeuralNetwork.mem_safeSet hf X h hx

/-- Robust classification, discharged by the same bound per rival label. -/
example {nn : NeuralNetwork (Zonotope 𝕋) 2 2} {f : Vec ℝ 2 → Vec ℝ 2}
    (hf : nn.Sound f) (X : Zonotope 𝕋 2) (l : Fin 2)
    (u : ∀ j, SupportBound (construct (nn.enclose X)) (marginDir 2 j l))
    (h : ∀ j, j ≠ l → (u j).val < 0) {x : Vec ℝ 2} (hx : x ∈ construct X)
    {j : Fin 2} (hj : j ≠ l) : f x j < f x l :=
  NeuralNetwork.classifies hf X l u h hx hj

/-- The network above is one of those, which is the only thing left to check. -/
example (W₁ : Mat 𝕋 3 2) (b₁ : Vec 𝕋 3) (W₂ : Mat 𝕋 2 3) (b₂ : Vec 𝕋 2)
    (X : Zonotope 𝕋 2) : Zonotope 𝕋 2 :=
  (Example.feedForward W₁ b₁ W₂ b₂).enclose X

/-- Sigmoid and tanh in one chain, and it is a `def`: `Layer` stores nothing
that mentions `ℝ`, so nothing here is noncomputable. -/
def Example.sigmoidTanhNet (k : ℕ) (W₁ : Mat 𝕋 3 2) (b₁ : Vec 𝕋 3) (W₂ : Mat 𝕋 2 3)
    (b₂ : Vec 𝕋 2) : NeuralNetwork (Zonotope 𝕋) 2 2 :=
  .cons (Layer.linear (S := Zonotope 𝕋) W₁ b₁)
    (.cons (Layer.sigmoid k) (.cons (Layer.linear W₂ b₂) (.cons (Layer.tanh k) .nil)))

/-- And what it computes, which is where `Real.sigmoid` and `Real.tanh` appear. -/
theorem Example.sigmoidTanhNet_sound (k : ℕ) (W₁ : Mat 𝕋 3 2) (b₁ : Vec 𝕋 3)
    (W₂ : Mat 𝕋 2 3) (b₂ : Vec 𝕋 2) :
    (Example.sigmoidTanhNet k W₁ b₁ W₂ b₂).Sound fun x i =>
      Real.tanh ((Scalar.toRealMat W₂ *ᵥ (fun j =>
          Real.sigmoid ((Scalar.toRealMat W₁ *ᵥ x + Scalar.toRealVec b₁) j))
        + Scalar.toRealVec b₂) i) :=
  (NeuralNetwork.sound_cons (Layer.linear_sound W₁ b₁)
    (NeuralNetwork.sound_cons (Layer.sigmoid_sound k)
      (NeuralNetwork.sound_cons (Layer.linear_sound W₂ b₂)
        (NeuralNetwork.ofLayer_sound (Layer.tanh_sound k))))).congr fun _ => rfl

/-- The polynomial relaxation in a chain, over a float polynomial zonotope, and
a `def` for the same reason: the fits and the grids are floats. -/
def Example.sigmoidPolyNet (k : ℕ) (W₁ : Mat 𝕋 3 2) (b₁ : Vec 𝕋 3) (W₂ : Mat 𝕋 2 3)
    (b₂ : Vec 𝕋 2) (c : Fin 3 → 𝕋 → 𝕋 → Fin 3 → 𝕋) (dx : Fin 3 → 𝕋 → 𝕋 → 𝕋)
    (p : Fin 3 → 𝕋 → 𝕋 → Fin 5 → 𝕋) : NeuralNetwork (PolyZonotope 𝕋) 2 2 :=
  .cons (Layer.linear (S := PolyZonotope 𝕋) W₁ b₁)
    (.cons (Layer.sigmoidPoly k c dx p) (.cons (Layer.linear W₂ b₂) .nil))

/-- And what it computes, `Real.sigmoid` arriving only here. -/
theorem Example.sigmoidPolyNet_sound (k : ℕ) (W₁ : Mat 𝕋 3 2) (b₁ : Vec 𝕋 3)
    (W₂ : Mat 𝕋 2 3) (b₂ : Vec 𝕋 2) (c : Fin 3 → 𝕋 → 𝕋 → Fin 3 → 𝕋) (dx : Fin 3 → 𝕋 → 𝕋 → 𝕋)
    (p : Fin 3 → 𝕋 → 𝕋 → Fin 5 → 𝕋) :
    (Example.sigmoidPolyNet k W₁ b₁ W₂ b₂ c dx p).Sound fun x =>
      Scalar.toRealMat W₂ *ᵥ (fun j =>
          Real.sigmoid ((Scalar.toRealMat W₁ *ᵥ x + Scalar.toRealVec b₁) j))
        + Scalar.toRealVec b₂ :=
  (NeuralNetwork.sound_cons (Layer.linear_sound W₁ b₁)
    (NeuralNetwork.sound_cons (Layer.sigmoidPoly_sound k c dx p)
      (NeuralNetwork.ofLayer_sound (Layer.linear_sound W₂ b₂)))).congr fun _ => rfl

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
