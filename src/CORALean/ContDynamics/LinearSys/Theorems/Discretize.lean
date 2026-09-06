import CORALean.ContDynamics.LinearSys.Operations.Discretize
import CORALean.ContDynamics.LinearSys.Operations.InputSolution
import CORALean.ContDynamics.LinearSys.Operations.StepInput
import CORALean.ContDynamics.LinearSys.Theorems.DiscretizeStep
import CORALean.ContDynamics.LinearSys.Theorems.StepSubset

/-!
# A sampled trajectory is a trajectory of the sampled system

Reading a continuous run at `0, Δt, 2Δt, ...` gives a run of `discretize`, so
every guarantee `LinearSysDT` already carries applies at the sample times.
Every step at once, so the domain has to be all of forward time: the discrete
trajectory produced is indexed by all of `ℕ`, and `LinearSysDT.Trajectory` has
no partial form. A bounded domain goes through `reach_outer_horizon` instead.
-/

-- Authors:       Tobias Ladner
-- Written:       18-August-2026
-- Last update:   02-September-2026
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix ContSet Scalar

variable {n : ℕ} {𝕋 : Type} [Scalar 𝕋]
variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]
variable [∀ n, Plus (S n) (Vec ℝ n)] [∀ n, LinComb (S n) (Vec ℝ n)]
variable [∀ n, Reduce (S n) (Vec ℝ n)] [Mtimes (Mat ℝ) S]

omit [∀ n, Plus (S n) (Vec ℝ n)] [∀ n, LinComb (S n) (Vec ℝ n)]
  [∀ n, Reduce (S n) (Vec ℝ n)] [Mtimes (Mat ℝ) S] in


-- =======================================  MAIN THEOREM  ======================================= --

theorem LinearSys.Trajectory.discretize {sys : LinearSys 𝕋 n} {T : Set ℝ} {R₀ U Ud : S n}
    {x u : ℝ → Vec ℝ n} {Δt : ℝ} (traj : sys.Trajectory T R₀ U x u) (hΔt : 0 ≤ Δt)
    (hT : Set.Ici 0 ⊆ T) (hU : Bornology.IsBounded (construct U))
    (hUd : ∀ k : ℕ, sys.stepInput u Δt k ∈ construct Ud) :
    (sys.discretize Δt).Trajectory R₀ Ud (fun k : ℕ => x (k * Δt)) (sys.stepInput u Δt) where
  init := by simpa using traj.init
  input k := hUd k
  step k := by
    simpa using traj.discretize_step hΔt hU k (step_subset hΔt hT k)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
