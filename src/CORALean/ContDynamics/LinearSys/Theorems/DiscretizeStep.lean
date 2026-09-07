import CORALean.ContDynamics.LinearSys.Operations.Discretize
import CORALean.ContDynamics.LinearSys.Operations.StepInput
import CORALean.ContDynamics.LinearSys.Theorems.InputIntegrable
import CORALean.ContDynamics.LinearSys.Theorems.VariationOfConstants

/-!
# One step of the sampled recursion

Variation of constants over `[kΔt, (k+1)Δt]`, where the propagator is
`e^{AΔt}` whatever `k` is: every bounded-horizon statement is this iterated, so
it is stated apart from `discretize`, which needs every step at once.
-/

-- Authors:       Tobias Ladner
-- Written:       18-August-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix ContSet Scalar

variable {n : ℕ} {𝕋 : Type} [Scalar 𝕋]
variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]


-- =======================================  MAIN THEOREM  ======================================= --

theorem LinearSys.Trajectory.discretize_step {sys : LinearSys 𝕋 n} {T : Set ℝ}
    {R₀ U : S n} {x u : ℝ → Vec ℝ n} {Δt : ℝ} (traj : sys.Trajectory T R₀ U x u)
    (hΔt : 0 ≤ Δt) (hU : Bornology.IsBounded (construct U)) (k : ℕ)
    (hT : Set.Icc ((k : ℝ) * Δt) (((k : ℝ) + 1) * Δt) ⊆ T) :
    x (((k : ℝ) + 1) * Δt)
      = toRealMat (sys.discretize Δt).A *ᵥ x ((k : ℝ) * Δt)
        + sys.stepInput u Δt k := by -- --- PROOF ---
  have hab : (k : ℝ) * Δt ≤ ((k : ℝ) + 1) * Δt := by nlinarith [Nat.cast_nonneg (α := ℝ) k]
  have h := traj.variation_of_constants hT hab (traj.intervalIntegrable_input hT hab hU)
  have hstep : ((k : ℝ) + 1) * Δt - (k : ℝ) * Δt = Δt := by ring
  rw [hstep] at h
  simpa [LinearSys.discretize, LinearSys.stepInput] using h

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
