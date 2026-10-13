import CORALean.ContSet.Conversion.Real.API
import CORALean.NN.Layers.Definitions.Enclosure
import CORALean.NN.Layers.Definitions.Relaxation
import CORALean.NN.Layers.Definitions.Relu
import CORALean.NN.Layers.Instances
import CORALean.NN.Layers.Operations.Linear
import CORALean.NN.Layers.Operations.Relu
import CORALean.NN.Layers.Operations.ReluSlope
import CORALean.NN.Theorems.Classifies
import CORALean.NN.Theorems.EncloseOuter
import CORALean.NN.Theorems.MarginDir
import CORALean.NN.Theorems.MemSafeSet

/-!
# A feed-forward network, verified end to end

The pipeline at a representation, which is the thing a set of interfaces cannot
promise on its own: `Zonotope` supplies `Mtimes`, `Plus`, a box it produces and
a box it absorbs, and that is exactly what the linear and ReLU layers ask for,
so the network below elaborates with no further instances.

Compiled, so it is a regression test as much as an example. It fails the moment
an instance stops resolving, which is what a use site — and nothing in the
library itself — is able to notice.

Nothing here evaluates to a number, and that is the layer's job description
rather than a limitation: over ℝ every operation is noncomputable, since
ordering reals is. `Float` is where the same network produces bounds.

One Lean detail a first use site trips over: `S : ℕ → Type` cannot be read off
`S 3`, so a call has to name the family — `(S := 𝒵)` — and naming it once at
the first layer is enough, the rest of the network following from it.
-/

-- Authors:       Claude Opus 5
-- Written:       02-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix ContSet


-- =====================================  MAIN DEFINITION  ====================================== --

/-- Affine, ReLU, affine: two inputs, three hidden neurons, two labels. -/
noncomputable def Example.feedForward (W₁ : Mat ℝ 3 2) (b₁ : Vec ℝ 3) (W₂ : Mat ℝ 2 3)
    (b₂ : Vec ℝ 2) : NeuralNetwork 𝒵 2 2 :=
  .layer (LinearLayer.mk W₁ b₁)
    (.layer (ReluLayer.mk (𝕋 := ℝ) reluSlope rfl) (.layer (LinearLayer.mk W₂ b₂) .output))

-- anonymous, since their content is that they elaborate at this network

/-- Every output over the whole input set is in the zonotope that comes back. -/
example {nn : NeuralNetwork 𝒵 2 2} {f : Vec ℝ 2 → Vec ℝ 2} (hf : nn.Sound f)
    (X : Zonotope (Vec ℝ 2)) {x : Vec ℝ 2}
    (hx : x ∈ construct X) : f x ∈ construct (nn.enclose X) :=
  hf.enclose_outer X x hx

/-- A safe set the enclosed zonotope stays inside is a safe set every output
stays inside. -/
example {nn : NeuralNetwork 𝒵 2 2} {f : Vec ℝ 2 → Vec ℝ 2} (hf : nn.Sound f)
    (X : Zonotope (Vec ℝ 2)) {safe : Set (Vec ℝ 2)}
    (h : construct (nn.enclose X) ⊆ safe) {x : Vec ℝ 2} (hx : x ∈ construct X) :
    f x ∈ safe :=
  NeuralNetwork.mem_safeSet hf X h hx

/-- Robust classification at two labels, so a single bound decides it: label `l`
wins everywhere on `X` as soon as the rival cannot reach it. -/
example {nn : NeuralNetwork 𝒵 2 2} {f : Vec ℝ 2 → Vec ℝ 2} (hf : nn.Sound f)
    (X : Zonotope (Vec ℝ 2)) (l : Fin 2)
    (u : ∀ j, SupportBound (construct (nn.enclose X)) (marginDir 2 j l))
    (h : ∀ j, j ≠ l → (u j).val < 0) {x : Vec ℝ 2} (hx : x ∈ construct X)
    {j : Fin 2} (hj : j ≠ l) : f x j < f x l :=
  NeuralNetwork.classifies hf X l u h hx hj

/-- The network above is one of those, which is the only thing left to check. -/
noncomputable example (W₁ : Mat ℝ 3 2) (b₁ : Vec ℝ 3) (W₂ : Mat ℝ 2 3) (b₂ : Vec ℝ 2)
    (X : Zonotope (Vec ℝ 2)) : Zonotope (Vec ℝ 2) :=
  (Example.feedForward W₁ b₁ W₂ b₂).enclose X

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
