module

public import CORALean.ContDynamics.LinearSys.Theorems.ReachOuter
public import CORALean.ContDynamics.NonlinearSys.Theorems.Linearize
public import CORALean.ContDynamics.NonlinearSys.Theorems.Restrict

@[expose] public section

/-!
# The nonlinear reachable set is the linearized one

The payoff, [1, Sec. IV-A]: nothing new is computed for a nonlinear system. Once `linearize` has
turned the run into a run of the linear canonical form,
`LinearSys.IsCanonicalTrajectory.reach_outer` is the whole proof. The nonlinearity is paid for
entirely in `linInput`, so `reach_outer_inputSolution` differs from its linear counterpart only
in a widened `U` and a confinement hypothesis. `exp` takes the `l∞` operator norm on `Mat`, a
choice. `reach_outer` leaves the discrete input set to the caller and asks confinement of all
forward time; the `_horizon` and `_inputSolution` variants relax each in turn.

## Inputs
* `sys` – system
* `T` – time set
* `R₀` – initial set
* `Ud` – discrete input set
* `L` – remainder set
* `U` – input set
* `x` – state trajectory
* `u` – input trajectory
* `A` – state Jacobian
* `B` – input Jacobian
* `xs` – state expansion point
* `us` – input expansion point
* `R` – state region
* `Δt` – step size
* `y` – output trajectory
* `cert` – abstraction-error certificate
* `o` – maximum order
* `k` – sample index

## Hypotheses
* `traj` – trajectory of the system
* `hT` – nonnegative times in time set
* `hR` – trajectory stays in region
* `hΔt` – step size nonnegative
* `hU` – widened input bounded
* `hUd` – discrete input set holds the step inputs
* `ho` – order positive

## Conclusion
* the state at each sample lies in the linearized reachable set

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
theorem NonlinearSys.IsTrajectory.reach_outer {sys : NonlinearSys n m} {T : Set ℝ}
    {R₀ Ud L : S n} {U : S m} {x : ℝ → Vec ℝ n} {u : ℝ → Vec ℝ m}
    {A : Mat ℝ n n} {B : Mat ℝ n m} {xs : Vec ℝ n} {us : Vec ℝ m}
    {R : Set (Vec ℝ n)} {Δt : ℝ} {y : ℝ → Vec ℝ sys.q} (traj : sys.IsTrajectory T R₀ U x u y)
    (cert : AbstractionError sys.f A B xs us R (construct U) L)
    (hT : Set.Ici 0 ⊆ T) (hR : ∀ t : ℝ, 0 ≤ t → x t ∈ R) (hΔt : 0 ≤ Δt)
    (hU : Bornology.IsBounded (construct (linInput sys.f A B xs us U L)))
    (hUd : ∀ k : ℕ, (NonlinearSys.linearize A).stepInput
      (fun t => sys.f (x t) (u t) - A *ᵥ x t) Δt k ∈ construct Ud) {o : ℕ} (ho : 0 < o)
    (k : ℕ) : -- --- CONCL ---
    x (k * Δt) ∈
      construct (((NonlinearSys.linearize A).discretize Δt).reach ⟨R₀, Ud, 0, k⟩ ⟨o, ho⟩) :=
  ((traj.restrict hT).linearize measurableSet_Ici cert hR).reach_outer hΔt subset_rfl hU hUd ho k

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
