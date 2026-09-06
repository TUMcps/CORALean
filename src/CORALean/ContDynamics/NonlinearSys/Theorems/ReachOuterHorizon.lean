import CORALean.ContDynamics.LinearSys.Theorems.ReachOuterHorizon
import CORALean.ContDynamics.NonlinearSys.Theorems.LinearizeHorizon

/-!
# The nonlinear reachable set is the linearized one, over a bounded horizon

The one-step statement: confinement on `[0, KΔt]` alone puts the run inside
the linearized reachable set at every sample time of that horizon, assuming
nothing past `KΔt` — which is what re-linearizing from there needs.
-/

-- Authors:       Tobias Ladner
-- Written:       02-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix ContSet Scalar NormedSpace Plus Mtimes OfInterval

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {n m : ℕ}
variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]
variable [∀ n, Plus (S n) (Vec ℝ n)] [∀ n, Reduce (S n) (Vec ℝ n)]
variable [Mtimes (Mat ℝ) S] [OfInterval S]


-- =======================================  MAIN THEOREM  ======================================= --

/-- The one-step statement: confinement on `[0, KΔt]` alone puts the run inside
the linearized reachable set at every sample time of that horizon, assuming
nothing past `KΔt` — which is what re-linearizing from there needs. -/
theorem NonlinearSys.Trajectory.reach_outer_horizon {sys : NonlinearSys n m} {T : Set ℝ}
    {R₀ Ud L : S n} {U : S m} {x : ℝ → Vec ℝ n} {u : ℝ → Vec ℝ m}
    {A : Mat ℝ n n} {B : Mat ℝ n m} {xs : Vec ℝ n} {us : Vec ℝ m}
    {R : Set (Vec ℝ n)} {Δt : ℝ} {K : ℕ} (traj : sys.Trajectory T R₀ U x u)
    (cert : AbstractionError sys.f A B xs us R (construct U) L)
    (hT : Set.Icc 0 ((K : ℝ) * Δt) ⊆ T)
    (hR : ∀ t ∈ Set.Icc (0 : ℝ) ((K : ℝ) * Δt), x t ∈ R) (hΔt : 0 ≤ Δt)
    (hU : Bornology.IsBounded (construct (linInput sys.f A B xs us U L)))
    (hUd : ∀ k < K, (NonlinearSys.linearize A).stepInput
      (fun t => sys.f (x t) (u t) - A *ᵥ x t) Δt k ∈ construct Ud) (o : ℕ) :
    ∀ k ≤ K, x ((k : ℝ) * Δt) ∈
      construct (((NonlinearSys.linearize A).discretize Δt).reach o R₀ Ud k) :=
  (traj.linearize_horizon cert hT hR).reach_outer_horizon hΔt subset_rfl hU hUd o

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
