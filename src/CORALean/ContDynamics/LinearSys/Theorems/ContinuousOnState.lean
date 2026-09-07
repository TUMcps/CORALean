import CORALean.ContDynamics.LinearSys.LinearSys

/-!
# The state is continuous wherever the flow holds

Differentiable where the flow holds, hence continuous there. Needed twice over
by `InputIntegrable` — once to carry measurability of the state to the drift
term directly, once again after the reflection `τ ↦ c - τ`
`aestronglyMeasurable_input_reflected` composes it with — so it is stated once
here rather than proved inline at either call site.
-/

-- Authors:       Tobias Ladner
-- Written:       19-August-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open ContSet Scalar

variable {n : ℕ} {𝕋 : Type} [Scalar 𝕋]
variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]


-- =======================================  MAIN THEOREM  ======================================= --

theorem LinearSys.Trajectory.continuousOn_state {sys : LinearSys 𝕋 n} {T : Set ℝ}
    {R₀ U : S n} {x u : ℝ → Vec ℝ n} (traj : sys.Trajectory T R₀ U x u) : ContinuousOn x T :=
  fun t ht => (traj.flow t ht).continuousWithinAt

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
