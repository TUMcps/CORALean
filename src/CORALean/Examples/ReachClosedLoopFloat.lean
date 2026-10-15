import CORALean.ContDynamics.LinearSysDT.Operations.CanonicalFloat
import CORALean.ContDynamics.NeurNetContrSysDT.Theorems.HoldsOfCheck
import CORALean.ContDynamics.NeurNetContrSysDT.Theorems.ReachOuter
import CORALean.ContSet.Interval.Float.Instances
import CORALean.ContSet.Zonotope.Float.Instances
import CORALean.NN.Layers.Definitions.Enclosure
import CORALean.NN.Layers.Definitions.Relaxation
import CORALean.NN.Layers.Definitions.Relu
import CORALean.NN.Layers.Instances
import CORALean.NN.Layers.Operations.Linear
import CORALean.NN.Layers.Operations.Basic
import CORALean.NN.Layers.Operations.ReluSlope
import CORALean.Specification.Instances

/-!
# A network in a discrete-time loop, at a floating-point representation

`ReachFloat`'s claim for a controller: `NeurNetContrSysDT.reach` — controller on the reached
set, then the plant step — is written against `Scalar 𝕋` and the operation classes, so it runs at
a float zonotope with every declaration `:=` and nothing else. The loop is affine, ReLU,
affine with a two-state plant; the exact layer's soundness theorem is read at it, and a box safe
set is checked on the computed zonotope. The `def`s are `def` rather than `noncomputable def`,
as are `Sigmoid`, `Tanh`, `Softmax`, `maxPool` and `SigmoidPoly`: `Layer` stores no function.
-/

-- Authors:       Claude Opus 5, Claude Opus 5.5
-- Written:       03-September-2026
-- Last update:   15-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open Matrix ContSet

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n r : ℕ} {L : Type}

/-- Affine, ReLU, affine, in the loop with a two-state plant. -/
def Example.closedLoopFloat (A : Mat 𝕋 2 2) (W₁ : Mat 𝕋 3 2) (b₁ : Vec 𝕋 3)
    (W₂ : Mat 𝕋 2 3) (b₂ : Vec 𝕋 2) : NeurNetContrSysDT (LinearSysDT 𝕋 2) 𝒵[𝕋] 2 :=
  ⟨LinearSysDT.canonicalFloat A, .layer (LinearLayer.mk W₁ b₁)
    (.layer (ReluLayer.mk (𝕋 := 𝕋) reluSlope rfl) (.layer (LinearLayer.mk W₂ b₂) .output))⟩


-- =====================================  MAIN DEFINITION  ====================================== --

def Example.reachClosedLoopFloat (sys : NeurNetContrSysDT (LinearSysDT 𝕋 n) 𝒵[𝕋] n)
    (o : ℕ) (ho : 0 < o) (R₀ : Zonotope (Vec 𝕋 n)) (k : ℕ) : Zonotope (Vec 𝕋 n) :=
  sys.reach ⟨R₀, 0, k⟩ ⟨o, ho⟩

example (sys : NeurNetContrSysDT (LinearSysDT 𝕋 n) 𝒵[𝕋] n) {o : ℕ} (ho : 0 < o)
    (R₀ : Zonotope (Vec 𝕋 n)) {π : Vec ℝ n → Vec ℝ sys.plant.m} (hπ : sys.contr.Sound π)
    {x : ℕ → Vec ℝ n} {w : ℕ → Vec ℝ sys.plant.r}
    (traj : sys.Trajectory π R₀ {0} x w) (k : ℕ) :
    x k ∈ construct (sys.reach ⟨R₀, 0, k⟩ ⟨o, ho⟩) :=
  sys.reach_outer (S := 𝒵[𝕋]) ho R₀ hπ
    (fun v hv => by rw [Set.mem_singleton_iff.1 hv, Matrix.mulVec_zero]) traj k

/-- A box safe set checked on the closed loop's computed zonotope. -/
example (sys : NeurNetContrSysDT (LinearSysDT 𝕋 n) 𝒵[𝕋] n) {o : ℕ} (ho : 0 < o)
    (R₀ : Zonotope (Vec 𝕋 n)) (spec : Specification (Interval (Vec 𝕋 n)))
    {π : Vec ℝ n → Vec ℝ sys.plant.m}
    (hπ : sys.contr.Sound π) {x : ℕ → Vec ℝ n} {w : ℕ → Vec ℝ sys.plant.r}
    (traj : sys.Trajectory π R₀ {0} x w) (k : ℕ) :
    spec.check (sys.reach ⟨R₀, 0, k⟩ ⟨o, ho⟩) → (spec.Holds {x k}) :=
  sys.holds_of_check (S := 𝒵[𝕋]) ho R₀ spec hπ
    (fun v hv => by rw [Set.mem_singleton_iff.1 hv, Matrix.mulVec_zero]) traj k

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
