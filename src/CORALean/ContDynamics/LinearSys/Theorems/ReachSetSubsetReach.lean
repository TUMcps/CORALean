module

public import CORALean.ContDynamics.LinearSys.Operations.StepInput
public import CORALean.ContDynamics.LinearSys.Definitions.ReachSet
public import CORALean.ContDynamics.LinearSys.Theorems.ReachOuter

@[expose] public section

/-!
# `reach` encloses the set the flow reaches, at the sample times

`reach_outer` with the trajectory quantifier moved off the front: what it says
of every run at `kΔt`, this says of the set of them at once, so a specification
about `reachSet` meets a bound on `reach` as one inclusion.

`Ud` is any set covering what an input can contribute over a step, and the
hypothesis is that same condition over every admissible run rather than over
one — `stepInput_outer` supplies it, and
`ReachSetSubsetTimeIntervalInputSolution` is the shape where nothing is left to
supply.

Between the sample times this says nothing; that is
`reachSet_subset_timeInterval_inputSolution`.
-/

-- Authors:       Claude Opus 5
-- Written:       07-September-2026
-- Last update:   30-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix ContSet Scalar

variable {n : ℕ} {𝕋 : Type} [Scalar 𝕋]
variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]
variable [∀ n, Plus (S n) (Vec ℝ n)] [∀ n, Reduce (S n) (Vec ℝ n)] [Mtimes (Mat ℝ) S]


-- =======================================  MAIN THEOREM  ======================================= --

/-- Reach for this where the input enclosure is already in hand; the guarantee
attaches to the reachable set, not to a run of it. -/
theorem LinearSys.reachSet_subset_reach (sys : LinearSys 𝕋 n) {T : Set ℝ} (R₀ U Ud : S n)
    {Δt : ℝ} (hΔt : 0 ≤ Δt) (hT : Set.Ici 0 ⊆ T) (hU : Bornology.IsBounded (construct U))
    (hUd : ∀ x u : ℝ → Vec ℝ n, sys.Trajectory T R₀ U x u →
      ∀ k : ℕ, sys.stepInput u Δt k ∈ construct Ud) {o : ℕ} (ho : 0 < o) (k : ℕ) :
    sys.reachSet T R₀ U ((k : ℝ) * Δt)
      ⊆ construct ((sys.discretize Δt).reach ⟨R₀, Ud, 0, k⟩ ⟨o, ho⟩) := by
  rintro _ ⟨x, u, traj, rfl⟩
  exact traj.reach_outer hΔt hT hU (hUd x u traj) ho k

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
