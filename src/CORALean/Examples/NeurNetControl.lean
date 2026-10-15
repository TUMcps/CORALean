import CORALean.ContDynamics.NeurNetContrSys.Theorems.HoldsOfReach
import CORALean.ContDynamics.NeurNetContrSys.Theorems.OfFullTrajectoryIff
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
on their own: `Zonotope` supplies `Mtimes` at a plain and at an interval matrix, `Plus`, `Reduce`,
convexity, compactness and the two boxes the layers want, and that is everything the plant and the
controller ask for between them. If an instance ever stops resolving, this file is where the build
says so (`NeurNetControlDT` has the discrete-time loop).

The network drives every input of this plant (`NeurNetContrSys.ofFull`, `nExt = 0`); the abstract
systems below allow `m ≤ nrOfInputs`, the rest being external inputs `U_ext`, and
`Example.nnControlledExt` is one such loop. `Δt` is the reachability step, `N Δt` the control
period `dt`, and `N` is a variable so that nothing can quietly assume they are equal.

Compiled at concrete *types* and an abstract system, deliberately: applying a
general theorem to a fully concrete network forces the elaborator to whnf the
whole graph, which `FeedForward` records as a timeout.

Nothing here evaluates to a number: over ℝ every operation is noncomputable.
-/

-- Authors:       Claude Opus 5, Claude Opus 5.5, Claude Sonnet 5.5
-- Written:       02-September-2026
-- Last update:   15-October-2026
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
    (W₂ : Mat ℝ 2 3) (b₂ : Vec ℝ 2) (dt : ℝ) : NeurNetContrSys (LinearSys ℝ 2) 𝒵 2 :=
  NeurNetContrSys.ofFull (LinearSys.canonical A) (Example.nnController W₁ b₁ W₂ b₂) dt

/-- A controller with one output, for a plant with two inputs: `Example.nnControlledExt`'s
network. -/
noncomputable def Example.nnController₁ (W₁ : Mat ℝ 3 2) (b₁ : Vec ℝ 3) (W₂ : Mat ℝ 1 3)
    (b₂ : Vec ℝ 1) : NeuralNetwork 𝒵 2 1 :=
  .layer (LinearLayer.mk W₁ b₁)
    (.layer (ReluLayer.mk (𝕋 := ℝ) reluSlope rfl) (.layer (LinearLayer.mk W₂ b₂) .output))

/-- The same plant with the network driving only its first input; the second is external
(`nExt = 1`), free in `U_ext`. -/
noncomputable def Example.nnControlledExt (A : Mat ℝ 2 2) (W₁ : Mat ℝ 3 2) (b₁ : Vec ℝ 3)
    (W₂ : Mat ℝ 1 3) (b₂ : Vec ℝ 1) (dt : ℝ) : NeurNetContrSys (LinearSys ℝ 2) 𝒵 2 where
  plant := LinearSys.canonical A
  m := 1
  hm := Nat.le_succ 1
  contr := Example.nnController₁ W₁ b₁ W₂ b₂
  dt := dt

-- anonymous, since their content is that they elaborate at this representation

/-- Every zero-order-hold run is inside the two-rate recursion at every control
period boundary — `N` reachability steps of length `Δt` per period. -/
example (sys : NeurNetContrSys (LinearSys ℝ 2) 𝒵 2) (U_ext : Zonotope (Vec ℝ sys.nExt))
    (R₀ : Zonotope (Vec ℝ 2)) (o η N : ℕ) (ho : 0 < o)
    {Δt : ℝ} (hΔt : 0 < Δt)
    (hdt : sys.dt = (N : ℝ) * Δt) (hε : ‖Δt • sys.augment.A‖ / ((η : ℝ) + 2) < 1) {H : ℕ}
    {π : Vec ℝ 2 → Vec ℝ sys.m} (hπ : sys.contr.Sound π)
    {x : ℝ → Vec ℝ 2} {v : ℝ → Vec ℝ sys.nExt} {w : ℝ → Vec ℝ sys.plant.r}
    (traj : sys.Trajectory π H R₀ (construct U_ext) {0} x v w) (i : ℕ)
    (hi : i ≤ H) :
    x ((i : ℝ) * sys.dt) ∈
      construct (sys.reach U_ext ⟨R₀, 0, i⟩ ⟨Δt, N, η, o, ho⟩) :=
  sys.reach_outer U_ext o η N ho hΔt hdt hε hπ
    (fun v hv => by rw [Set.mem_singleton_iff.1 hv, Matrix.mulVec_zero]) traj i hi

/-- The same checked against a safe set. -/
example (sys : NeurNetContrSys (LinearSys ℝ 2) 𝒵 2) (U_ext : Zonotope (Vec ℝ sys.nExt))
    (R₀ : Zonotope (Vec ℝ 2)) (o η N : ℕ) (ho : 0 < o)
    {Δt : ℝ} (hΔt : 0 < Δt)
    (hdt : sys.dt = (N : ℝ) * Δt) (hε : ‖Δt • sys.augment.A‖ / ((η : ℝ) + 2) < 1) {H : ℕ}
    (safe : Set (Vec ℝ 2)) {π : Vec ℝ 2 → Vec ℝ sys.m} (hπ : sys.contr.Sound π)
    {x : ℝ → Vec ℝ 2} {v : ℝ → Vec ℝ sys.nExt} {w : ℝ → Vec ℝ sys.plant.r}
    (traj : sys.Trajectory π H R₀ (construct U_ext) {0} x v w) (i : ℕ)
    (hi : i ≤ H)
    (h : (Specification.safeSet safe).Holds
      (construct (sys.reach U_ext ⟨R₀, 0, i⟩ ⟨Δt, N, η, o, ho⟩))) :
    (Specification.safeSet safe).Holds {x ((i : ℝ) * sys.dt)} :=
  sys.holds_of_reach U_ext o η N ho hΔt hdt hε hπ
    (fun v hv => by rw [Set.mem_singleton_iff.1 hv, Matrix.mulVec_zero]) traj _ i hi h

/-- With the network driving every input, a run of the loop is a run of the plant under the
network's output alone, whatever the (nonempty) set of external inputs. -/
example (A : Mat ℝ 2 2) (W₁ : Mat ℝ 3 2) (b₁ : Vec ℝ 3) (W₂ : Mat ℝ 2 3) (b₂ : Vec ℝ 2)
    (R₀ : Zonotope (Vec ℝ 2)) (π : Vec ℝ 2 → Vec ℝ 2) (dt : ℝ) (H : ℕ)
    (U_ext : Set (Vec ℝ (Example.nnControlled A W₁ b₁ W₂ b₂ dt).nExt)) (hU : U_ext.Nonempty)
    (x : ℝ → Vec ℝ 2) (v : ℝ → Vec ℝ (Example.nnControlled A W₁ b₁ W₂ b₂ dt).nExt)
    (w : ℝ → Vec ℝ 2) :
    (Example.nnControlled A W₁ b₁ W₂ b₂ dt).Trajectory π H R₀ U_ext {0} x v w ↔
      x 0 ∈ construct R₀ ∧ ∀ i < H, ContDynamics.Trajectory (LinearSys.canonical A)
        (Set.Icc 0 dt) Set.univ {π (x ((i : ℝ) * dt))} {0} (fun t => x ((i : ℝ) * dt + t))
        (fun _ => π (x ((i : ℝ) * dt))) (fun t => w ((i : ℝ) * dt + t)) :=
  NeurNetContrSys.ofFull_trajectory_iff _ _ _ hU

/-- The loop above is one of those, which is the only thing left to check: with no external input,
its `U_ext` is a set of `Vec ℝ 0`s. -/
noncomputable example (A : Mat ℝ 2 2) (W₁ : Mat ℝ 3 2) (b₁ : Vec ℝ 3) (W₂ : Mat ℝ 2 3)
    (b₂ : Vec ℝ 2) (R₀ : Zonotope (Vec ℝ 2)) (o η N : ℕ) (ho : 0 < o) (Δt dt : ℝ) (i : ℕ) :
    Zonotope (Vec ℝ 2) :=
  (Example.nnControlled A W₁ b₁ W₂ b₂ dt).reach (OfPoint.ofPoint 0) ⟨R₀, 0, i⟩ ⟨Δt, N, η, o, ho⟩

/-- The loop with an external input: the same reach, under an external input set `U_ext`. -/
noncomputable example (A : Mat ℝ 2 2) (W₁ : Mat ℝ 3 2) (b₁ : Vec ℝ 3) (W₂ : Mat ℝ 1 3)
    (b₂ : Vec ℝ 1) (U_ext : Zonotope (Vec ℝ 1)) (R₀ : Zonotope (Vec ℝ 2)) (o η N : ℕ)
    (ho : 0 < o) (Δt dt : ℝ) (i : ℕ) : Zonotope (Vec ℝ 2) :=
  (Example.nnControlledExt A W₁ b₁ W₂ b₂ dt).reach U_ext ⟨R₀, 0, i⟩ ⟨Δt, N, η, o, ho⟩

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
