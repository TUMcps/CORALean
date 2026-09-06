import CORALean.ContDynamics.LinearSys.Theorems.ReachOuter
import CORALean.ContDynamics.NonlinearSys.Theorems.Linearize
import CORALean.ContDynamics.NonlinearSys.Theorems.Restrict

/-!
# The nonlinear reachable set is the linearized one

The payoff: nothing new is computed for a nonlinear system. Once `linearize` has
turned the run into a linear one, `LinearSys.Trajectory.reach_outer` is the whole
proof and the enclosing set is the linear system's `reach`.

The nonlinearity is paid for entirely in `linInput`, which is why
`reach_outer_inputSolution` differs from its linear counterpart only in that
`U` has been widened and a confinement hypothesis added. `exp` needs a norm on
`Mat` — a choice, not an instance — and it is the `l∞` operator norm here as
everywhere `discretize` is.

`reach_outer` leaves the discrete input set to the caller and asks confinement
of all forward time; the `_horizon` and `_inputSolution` variants relax each of
those in turn.
-/

-- Authors:       Tobias Ladner
-- Written:       02-September-2026
-- Last update:   04-September-2026
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
      (fun t => sys.f (x t) (u t) - A *ᵥ x t) Δt k ∈ construct Ud) (o k : ℕ) :
    x (k * Δt) ∈
      construct (((NonlinearSys.linearize A).discretize Δt).reach o R₀ Ud k) :=
  ((traj.restrict hT).linearize cert hR).reach_outer hΔt subset_rfl hU hUd o k

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
