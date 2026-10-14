import CORALean.ContDynamics.NeurNetContrSys.Theorems.HoldsOfReach
import CORALean.ContSet.Conversion.Real.Instances
import CORALean.ContSet.Zonotope.Real.Instances
import CORALean.NN.Layers.Definitions.Enclosure
import CORALean.NN.Layers.Definitions.Relaxation
import CORALean.NN.Layers.Definitions.Relu
import CORALean.NN.Layers.Instances
import CORALean.NN.Layers.Operations.Linear
import CORALean.NN.Layers.Operations.Basic
import CORALean.NN.Layers.Operations.ReluSlope
import CORALean.ContDynamics.LinearSys.Operations.Canonical

/-!
# A continuous plant with a ReLU controller, verified end to end

The sampled-data loop at a representation, which is the thing the interfaces cannot promise
on their own: `Zonotope` supplies `Mtimes` at a plain and at an interval matrix,
`Plus`, `Reduce`, convexity, compactness and the two boxes the layers want, and
that is everything the plant and the controller ask for between them. If an
instance ever stops resolving, this file is where the build says so
(`NeurNetControlDT` has the discrete-time loop).

The two rates are visible here: `Δt` is the reachability
step, `N Δt` the control period, and `N` is a variable here precisely so that
nothing in the pipeline can quietly assume they are equal.

Compiled at concrete *types* and an abstract system, deliberately: applying a
general theorem to a fully concrete network forces the elaborator to whnf the
whole graph, which `FeedForward` records as a timeout.

Nothing here evaluates to a number: over ℝ every operation is noncomputable.
-/

-- Authors:       Claude Opus 5, Claude Opus 5.5, Claude Sonnet 5.5
-- Written:       02-September-2026
-- Last update:   14-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix ContSet Scalar

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

/-- Affine, ReLU, affine: two states in, three hidden neurons, two inputs back
out. The input is read straight as the plant's — neither plant carries a `B`, so
the controller's last layer is where an actuation matrix would go. -/
noncomputable def Example.nnController (W₁ : Mat ℝ 3 2) (b₁ : Vec ℝ 3) (W₂ : Mat ℝ 2 3)
    (b₂ : Vec ℝ 2) : NeuralNetwork 𝒵 2 2 :=
  .layer (LinearLayer.mk W₁ b₁)
    (.layer (ReluLayer.mk (𝕋 := ℝ) reluSlope rfl) (.layer (LinearLayer.mk W₂ b₂) .output))


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The same controller on a continuous plant, sampled. -/
noncomputable def Example.nnControlled (A : Mat ℝ 2 2) (W₁ : Mat ℝ 3 2) (b₁ : Vec ℝ 3)
    (W₂ : Mat ℝ 2 3) (b₂ : Vec ℝ 2) : NeurNetContrSys (LinearSys ℝ 2) 𝒵 2 where
  plant := LinearSys.canonical A
  contr := Example.nnController W₁ b₁ W₂ b₂

-- anonymous, since their content is that they elaborate at this representation

/-- Every zero-order-hold run is inside the two-rate recursion at every control
period boundary — `N` reachability steps of length `Δt` per period. -/
example (sys : NeurNetContrSys (LinearSys ℝ 2) 𝒵 2) (R₀ : Zonotope (Vec ℝ 2)) (o η N : ℕ)
    (ho : 0 < o)
    {Δt : ℝ} (hΔt : 0 < Δt) (hε : ‖Δt • sys.augment.A‖ / ((η : ℝ) + 2) < 1) {H : ℕ}
    {π : Vec ℝ 2 → Vec ℝ sys.plant.m} (hπ : sys.contr.Sound π)
    {W : Zonotope (Vec ℝ 0)} {x : ℝ → Vec ℝ 2} {w : ℝ → Vec ℝ 0}
    (traj : sys.Trajectory π ((N : ℝ) * Δt) H R₀ W x w) (i : ℕ) (hi : i ≤ H) :
    x ((i : ℝ) * ((N : ℝ) * Δt)) ∈ construct (sys.reach ⟨R₀, 0, i⟩ ⟨Δt, N, η, o, ho⟩) :=
  sys.reach_outer o η N ho hΔt hε hπ traj i hi

/-- The same checked against a safe set. -/
example (sys : NeurNetContrSys (LinearSys ℝ 2) 𝒵 2) (R₀ : Zonotope (Vec ℝ 2)) (o η N : ℕ)
    (ho : 0 < o)
    {Δt : ℝ} (hΔt : 0 < Δt) (hε : ‖Δt • sys.augment.A‖ / ((η : ℝ) + 2) < 1) {H : ℕ}
    (safe : Set (Vec ℝ 2)) {π : Vec ℝ 2 → Vec ℝ sys.plant.m} (hπ : sys.contr.Sound π)
    {W : Zonotope (Vec ℝ 0)} {x : ℝ → Vec ℝ 2} {w : ℝ → Vec ℝ 0}
    (traj : sys.Trajectory π ((N : ℝ) * Δt) H R₀ W x w) (i : ℕ) (hi : i ≤ H)
    (h : (Specification.safeSet safe).Holds (construct (sys.reach ⟨R₀, 0, i⟩ ⟨Δt, N, η, o, ho⟩))) :
    (Specification.safeSet safe).Holds {x ((i : ℝ) * ((N : ℝ) * Δt))} :=
  sys.holds_of_reach o η N ho hΔt hε hπ traj _ i hi h

/-- The loop above is one of those, which is the only thing left to check. -/
noncomputable example (A : Mat ℝ 2 2) (W₁ : Mat ℝ 3 2) (b₁ : Vec ℝ 3) (W₂ : Mat ℝ 2 3)
    (b₂ : Vec ℝ 2) (R₀ : Zonotope (Vec ℝ 2)) (o η N : ℕ) (ho : 0 < o) (Δt : ℝ) (i : ℕ) :
    Zonotope (Vec ℝ 2) :=
  (Example.nnControlled A W₁ b₁ W₂ b₂).reach ⟨R₀, 0, i⟩ ⟨Δt, N, η, o, ho⟩

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
