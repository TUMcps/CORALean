module

public import CORALean.ContDynamics.LinearSys.Operations.Discretize
public import CORALean.ContDynamics.LinearSys.Operations.InputSolution
public import CORALean.ContDynamics.LinearSys.Operations.StepInput
public import CORALean.ContDynamics.LinearSys.Theorems.DiscretizeStep
public import CORALean.ContDynamics.LinearSys.Theorems.StepSubset

@[expose] public section

/-!
# A sampled trajectory is a trajectory of the sampled system

Reading a continuous run at `0, Δt, 2Δt, ...` gives a run of `discretize`, so
every guarantee `LinearSysDT` already carries applies at the sample times.
Every step at once, so the domain has to be all of forward time: the discrete
trajectory produced is indexed by all of `ℕ`, and `LinearSysDT.IsCanonicalTrajectory` has
no partial form. A bounded domain goes through `reach_outer_horizon` instead.

## Inputs
* `sys` – linear system
* `T` – time domain
* `R₀` – initial set
* `U` – input set
* `Ud` – sampled input set
* `x` – state trajectory
* `u` – input signal
* `Δt` – sampling step

## Hypotheses
* `traj` – signal is a canonical trajectory
* `hΔt` – step length nonnegative
* `hT` – time domain contains the nonnegative reals
* `hU` – input set bounded
* `hUd` – step inputs lie in the sampled input set

## Conclusion
* the sampled trajectory is a trajectory of the sampled system
-/

-- Authors:       Claude Opus 5
-- Written:       18-August-2026
-- Last update:   02-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix ContSet Scalar

variable {n : ℕ} {𝕋 : Type} [Scalar 𝕋]
variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]
variable [∀ n, Plus (S n) (Vec ℝ n)] [∀ n, LinComb (S n) (Vec ℝ n)]
variable [∀ n, Reduce (S n) (Vec ℝ n)] [Mtimes (Mat ℝ) S]

omit [∀ n, Plus (S n) (Vec ℝ n)] [∀ n, LinComb (S n) (Vec ℝ n)]
  [∀ n, Reduce (S n) (Vec ℝ n)] [Mtimes (Mat ℝ) S] in


-- =======================================  MAIN THEOREM  ======================================= --

theorem LinearSys.IsCanonicalTrajectory.discretize {sys : LinearSys 𝕋 n} {T : Set ℝ} {R₀ U Ud : S n}
    {x u : ℝ → Vec ℝ n} {Δt : ℝ} (traj : sys.IsCanonicalTrajectory T R₀ U x u) (hΔt : 0 ≤ Δt)
    (hT : Set.Ici 0 ⊆ T) (hU : Bornology.IsBounded (construct U))
    (hUd : ∀ k : ℕ, sys.stepInput u Δt k ∈ construct Ud) :
    (sys.discretize Δt).IsCanonicalTrajectory R₀ Ud (fun k : ℕ => x (k * Δt)) (sys.stepInput u Δt)
        where
  init := by simpa using traj.init
  input k := hUd k
  step k := by
    simpa using traj.discretize_step hΔt hU k fun _ hs => hT hs.1

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
