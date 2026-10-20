module

public import CORALean.ContDynamics.LinearSys.Definitions.TimeIntervalReachSetExact

@[expose] public section

/-!
# `timeIntervalReachSetExact` contains every trajectory over the interval

The cheap half, as `ReachSetExactOuter` is for `reachSetExact`: a trajectory at any time
of `[0, r]` is in the set of what trajectories reach over `[0, r]` by
construction.

## Inputs
* `sys` – linear system
* `T` – time domain
* `R₀` – initial set
* `U` – input set
* `x` – state trajectory
* `u` – input signal
* `r` – interval end
* `t` – time

## Hypotheses
* `traj` – signal is a canonical trajectory
* `ht` – time lies in the interval

## Conclusion
* the trajectory's state at the time lies in the interval reach set
-/

-- Authors:       Claude Opus 5
-- Written:       11-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix ContSet Scalar

variable {n : ℕ} {𝕋 : Type} [Scalar 𝕋]
variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]


-- =======================================  MAIN THEOREM  ======================================= --

/-- Reach for this to say where a run is over the whole interval; reach for
`timeIntervalReachSetExact_eq_iUnion` to read it as a union of `reachSetExact`. -/
theorem LinearSys.IsCanonicalTrajectory.timeIntervalReachSetExact_outer {sys : LinearSys 𝕋 n}
    {T : Set ℝ} {R₀ U : S n} {x u : ℝ → Vec ℝ n} (traj : sys.IsCanonicalTrajectory T R₀ U x u)
    {r t : ℝ}
    (ht : t ∈ Set.Icc (0:ℝ) r) :
    x t ∈ sys.timeIntervalReachSetExact T R₀ U r :=
  ⟨x, u, traj, t, ht, rfl⟩

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
