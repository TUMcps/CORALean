import CORALean.ContDynamics.LinearSys.Theorems.ClassicalTrajectoryTrajectory
import CORALean.ContDynamics.LinearSys.Theorems.ReachOuter
import CORALean.ContDynamics.NonlinearSys.Theorems.Linearize
import CORALean.ContDynamics.NonlinearSys.Theorems.Restrict

/-!
# The nonlinear reachable set is the linearized one

The payoff, [1, Sec. IV-A]: nothing new is computed for a nonlinear system. Once `linearize` has
turned the run into a classical linear one, `ClassicalTrajectory.trajectory` and
`LinearSys.Trajectory.reach_outer` are the whole proof, the enclosing set the linear
system's `reach`.

The nonlinearity is paid for entirely in `linInput`, which is why
`reach_outer_inputSolution` differs from its linear counterpart only in that
`U` has been widened and a confinement hypothesis added. `exp` needs a norm on
`Mat` — a choice, not an instance — and it is the `l∞` operator norm here as
everywhere `discretize` is.

`reach_outer` leaves the discrete input set to the caller and asks confinement
of all forward time; the `_horizon` and `_inputSolution` variants relax each of
those in turn. Neither discharges confinement — `confinement_of_subset` does,
over the steps of a re-linearization loop.

## References

* [1] M. Althoff, O. Stursberg and M. Buss. "Reachability Analysis of Nonlinear
      Systems with Uncertain Parameters using Conservative Linearization". In
      Proc. of the 47th IEEE Conference on Decision and Control (CDC), 2008,
      pp. 4042-4048.
-/

-- Authors:       Claude Opus 5
-- Written:       02-September-2026
-- Last update:   30-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix ContSet Scalar NormedSpace Plus Mtimes Real.OfInterval

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {n m : ℕ}
variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]
variable [∀ n, Plus (S n) (Vec ℝ n)] [∀ n, Reduce (S n) (Vec ℝ n)]
variable [Mtimes (Mat ℝ) S] [Real.OfInterval S]


-- =======================================  MAIN THEOREM  ======================================= --

/-- A confined nonlinear run is inside the linearized system's reachable set at
every sample time. -/
theorem NonlinearSys.Trajectory.reach_outer {sys : NonlinearSys n m} {T : Set ℝ}
    {R₀ Ud L : S n} {U : S m} {x : ℝ → Vec ℝ n} {u : ℝ → Vec ℝ m}
    {A : Mat ℝ n n} {B : Mat ℝ n m} {xs : Vec ℝ n} {us : Vec ℝ m}
    {R : Set (Vec ℝ n)} {Δt : ℝ} (traj : sys.Trajectory T R₀ U x u)
    (cert : AbstractionError sys.f A B xs us R (construct U) L)
    (hT : Set.Ici 0 ⊆ T) (hR : ∀ t : ℝ, 0 ≤ t → x t ∈ R) (hΔt : 0 ≤ Δt)
    (hU : Bornology.IsBounded (construct (linInput sys.f A B xs us U L)))
    (hUd : ∀ k : ℕ, (NonlinearSys.linearize A).stepInput
      (fun t => sys.f (x t) (u t) - A *ᵥ x t) Δt k ∈ construct Ud) {o : ℕ} (ho : 0 < o) (k : ℕ) :
    x (k * Δt) ∈
      construct (((NonlinearSys.linearize A).discretize Δt).reach ⟨R₀, Ud, 0, k⟩ ⟨o, ho⟩) :=
  (((traj.restrict hT).linearize cert hR).trajectory (convex_Ici 0) Set.self_mem_Ici hU).reach_outer
    hΔt subset_rfl hU hUd ho k

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
