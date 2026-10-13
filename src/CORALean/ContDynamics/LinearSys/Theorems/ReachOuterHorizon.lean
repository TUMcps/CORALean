module

public import CORALean.ContDynamics.LinearSys.Theorems.DiscretizeHorizon
public import CORALean.ContDynamics.LinearSysDT.Theorems.ReachOuterOn

@[expose] public section

/-!
# `reach` contains every trajectory over a bounded horizon

The same conclusion as `reach_outer`, over a bounded horizon: `K` steps see the
flow on `[0, KΔt]` and nothing beyond. `discretize_horizon` handed to
`reach_outer_on` — no recursion of its own.
-/

-- Authors:       Claude Opus 5
-- Written:       18-August-2026
-- Last update:   30-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix ContSet Scalar

variable {n : ℕ} {𝕋 : Type} [Scalar 𝕋]
variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]
variable [∀ n, Plus (S n) (Vec ℝ n)] [∀ n, LinComb (S n) (Vec ℝ n)]
variable [∀ n, Reduce (S n) (Vec ℝ n)] [Mtimes (Mat ℝ) S]


-- =======================================  MAIN THEOREM  ======================================= --

omit [∀ n, LinComb (S n) (Vec ℝ n)] in
theorem LinearSys.Trajectory.reach_outer_horizon {sys : LinearSys 𝕋 n} {T : Set ℝ}
    {R₀ U Ud : S n} {x u : ℝ → Vec ℝ n} {Δt : ℝ} {K : ℕ}
    (traj : sys.Trajectory T R₀ U x u) (hΔt : 0 ≤ Δt)
    (hT : Set.Icc 0 ((K : ℝ) * Δt) ⊆ T) (hU : Bornology.IsBounded (construct U))
    (hUd : ∀ k < K, sys.stepInput u Δt k ∈ construct Ud) {o : ℕ} (ho : 0 < o) :
    ∀ k ≤ K, x ((k : ℝ) * Δt) ∈ construct ((sys.discretize Δt).reach ⟨R₀, Ud, 0, k⟩ ⟨o, ho⟩) :=
  (sys.discretize Δt).reach_outer_on ho R₀ Ud (traj.discretize_horizon hΔt hT hU hUd)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
