import CORALean.ContDynamics.NeurNetContrSys.Theorems.HoldsOfReach
import CORALean.ContDynamics.NeurNetContrSysDT.Theorems.EqOfInit
import CORALean.ContDynamics.NeurNetContrSysDT.Theorems.HoldsOfReach
import CORALean.ContSet.Conversion.Real.ContSet_to_Interval
import CORALean.ContSet.Conversion.Real.Interval_to_ContSet
import CORALean.ContSet.Zonotope.Real.Instances
import CORALean.NN.Layers.Linear
import CORALean.NN.Layers.ReLU

/-!
# A two-state plant with a ReLU controller, verified end to end

Both loops at a representation, which is the thing the interfaces cannot promise
on their own: `Zonotope` supplies `Mtimes` at a plain and at an interval matrix,
`Plus`, `Reduce`, convexity, compactness and the two boxes the layers want, and
that is everything the plant and the controller ask for between them. If an
instance ever stops resolving, this file is where the build says so.

The continuous loop is where the two rates are visible: `Δt` is the reachability
step, `N Δt` the control period, and `N` is a variable here precisely so that
nothing in the pipeline can quietly assume they are equal.

Compiled at concrete *types* and an abstract system, deliberately: applying a
general theorem to a fully concrete network forces the elaborator to whnf the
whole graph, which `FeedForward` records as a timeout.

Nothing here evaluates to a number. Over ℝ every operation is noncomputable, and
`Float` is where the same loops produce bounds.
-/

-- Authors:       Tobias Ladner
-- Written:       02-September-2026
-- Last update:   ---
-- Last revision: ---

namespace CORALean.Real

open Matrix ContSet Scalar

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

/-- Affine, ReLU, affine: two states in, three hidden neurons, two inputs back
out. The input is read straight as the plant's — neither plant carries a `B`, so
the controller's last layer is where an actuation matrix would go. -/
noncomputable def Example.nnController (W₁ : Mat ℝ 3 2) (b₁ : Vec ℝ 3) (W₂ : Mat ℝ 2 3)
    (b₂ : Vec ℝ 2) : NeuralNetwork 𝒵 2 2 :=
  .cons (Layer.linear (S := 𝒵) W₁ b₁)
    (.cons Layer.relu (.cons (Layer.linear W₂ b₂) .nil))

noncomputable def Example.nnControlledDT (A : Mat ℝ 2 2) (W₁ : Mat ℝ 3 2) (b₁ : Vec ℝ 3)
    (W₂ : Mat ℝ 2 3) (b₂ : Vec ℝ 2) : NeurNetContrSysDT ℝ 𝒵 2 where
  plant := ⟨A⟩
  contr := Example.nnController W₁ b₁ W₂ b₂

/-- The same controller on a continuous plant, sampled. -/
noncomputable def Example.nnControlled (A : Mat ℝ 2 2) (W₁ : Mat ℝ 3 2) (b₁ : Vec ℝ 3)
    (W₂ : Mat ℝ 2 3) (b₂ : Vec ℝ 2) : NeurNetContrSys ℝ 𝒵 2 where
  plant := ⟨A⟩
  contr := Example.nnController W₁ b₁ W₂ b₂

-- anonymous, since their content is that they elaborate at this representation

/-- Every discrete closed-loop run from `R₀` is inside the alternating recursion
at every step. -/
example (sys : NeurNetContrSysDT ℝ 𝒵 2) (R₀ : Zonotope (Vec ℝ 2)) (o : ℕ)
    {x : ℕ → Vec ℝ 2} (traj : sys.Trajectory R₀ x) (k : ℕ) :
    x k ∈ construct (sys.reach o R₀ k) :=
  sys.reach_outer o R₀ traj k

/-- A safe set the reached zonotope stays inside is a safe set the run stays
inside — `Specification.holds_of_outer`, reached from the loop. -/
example (sys : NeurNetContrSysDT ℝ 𝒵 2) (R₀ : Zonotope (Vec ℝ 2)) (o : ℕ)
    (safe : Set (Vec ℝ 2)) {x : ℕ → Vec ℝ 2} (traj : sys.Trajectory R₀ x) (k : ℕ)
    (h : (Specification.safeSet safe).Holds (construct (sys.reach o R₀ k))) :
    (Specification.safeSet safe).Holds {x k} :=
  sys.holds_of_reach o R₀ _ traj k h

/-- The discrete loop is deterministic, so a run is settled by where it
started. -/
example (sys : NeurNetContrSysDT ℝ 𝒵 2) (R₀ : Zonotope (Vec ℝ 2)) {x y : ℕ → Vec ℝ 2}
    (hx : sys.Trajectory R₀ x) (hy : sys.Trajectory R₀ y) (h : x 0 = y 0) : x = y :=
  hx.eq_of_init hy h

/-- Every zero-order-hold run is inside the two-rate recursion at every control
period boundary — `N` reachability steps of length `Δt` per period. -/
example (sys : NeurNetContrSys ℝ 𝒵 2) (R₀ : Zonotope (Vec ℝ 2)) (o η N : ℕ) {Δt : ℝ}
    (hΔt : 0 < Δt) (hε : ‖Δt • toRealMat sys.plant.A‖ / ((η : ℝ) + 2) < 1) {H : ℕ}
    {x : ℝ → Vec ℝ 2} (traj : sys.Trajectory ((N : ℝ) * Δt) H R₀ x) (i : ℕ) (hi : i ≤ H) :
    x ((i : ℝ) * ((N : ℝ) * Δt)) ∈ construct (sys.reach o η N Δt R₀ i) :=
  sys.reach_outer o η N hΔt hε traj i hi

/-- The same checked against a safe set. -/
example (sys : NeurNetContrSys ℝ 𝒵 2) (R₀ : Zonotope (Vec ℝ 2)) (o η N : ℕ) {Δt : ℝ}
    (hΔt : 0 < Δt) (hε : ‖Δt • toRealMat sys.plant.A‖ / ((η : ℝ) + 2) < 1) {H : ℕ}
    (safe : Set (Vec ℝ 2)) {x : ℝ → Vec ℝ 2} (traj : sys.Trajectory ((N : ℝ) * Δt) H R₀ x)
    (i : ℕ) (hi : i ≤ H)
    (h : (Specification.safeSet safe).Holds (construct (sys.reach o η N Δt R₀ i))) :
    (Specification.safeSet safe).Holds {x ((i : ℝ) * ((N : ℝ) * Δt))} :=
  sys.holds_of_reach o η N hΔt hε traj _ i hi h

/-- The loops above are ones of those, which is the only thing left to check. -/
noncomputable example (A : Mat ℝ 2 2) (W₁ : Mat ℝ 3 2) (b₁ : Vec ℝ 3) (W₂ : Mat ℝ 2 3)
    (b₂ : Vec ℝ 2) (R₀ : Zonotope (Vec ℝ 2)) (o k : ℕ) : Zonotope (Vec ℝ 2) :=
  (Example.nnControlledDT A W₁ b₁ W₂ b₂).reach o R₀ k

noncomputable example (A : Mat ℝ 2 2) (W₁ : Mat ℝ 3 2) (b₁ : Vec ℝ 3) (W₂ : Mat ℝ 2 3)
    (b₂ : Vec ℝ 2) (R₀ : Zonotope (Vec ℝ 2)) (o η N : ℕ) (Δt : ℝ) (i : ℕ) :
    Zonotope (Vec ℝ 2) :=
  (Example.nnControlled A W₁ b₁ W₂ b₂).reach o η N Δt R₀ i

end CORALean.Real
