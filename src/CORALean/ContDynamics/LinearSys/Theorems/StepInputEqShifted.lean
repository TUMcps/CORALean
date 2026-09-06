import CORALean.ContDynamics.LinearSys.Operations.StepInput

/-!
# One step of the input, read on a clock of its own

`stepInput_eq_shifted` moves step `k` to start at zero: the propagator only ever
sees the elapsed part of the step, so the shift leaves it alone and lands on the
integral over `[0, Δt]` that `inputSolution_outer` speaks about. `StepInputOuter`
is the one caller that needs this shifted form directly; `stepInput_shift`
reuses it to read the same identity the other way.

`exp` needs a norm on `Mat`, which is a choice rather than an instance, so this
file makes the same one as everything else reasoning about `stepInput` — the
`l∞` operator norm — or the terms would not match.
-/

-- Authors:       Tobias Ladner
-- Written:       02-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix Scalar NormedSpace MeasureTheory

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {n : ℕ} {𝕋 : Type} [Scalar 𝕋]


-- =======================================  MAIN THEOREM  ======================================= --

/-- Step `k` shifted to start at zero. -/
theorem LinearSys.stepInput_eq_shifted (sys : LinearSys 𝕋 n) (u : ℝ → Vec ℝ n) (Δt : ℝ)
    (k : ℕ) :
    sys.stepInput u Δt k
      = ∫ σ in (0:ℝ)..Δt, exp ((Δt - σ) • toRealMat sys.A) *ᵥ u ((k : ℝ) * Δt + σ) := by
  have hsplit : ((k : ℝ) + 1) * Δt = (k : ℝ) * Δt + Δt := by ring
  have hshift : ∀ σ : ℝ, (k : ℝ) * Δt + Δt - ((k : ℝ) * Δt + σ) = Δt - σ := fun σ => by ring
  have key := intervalIntegral.integral_comp_add_left (a := (0 : ℝ)) (b := Δt)
    (fun s : ℝ => exp (((k : ℝ) * Δt + Δt - s) • toRealMat sys.A) *ᵥ u s) ((k : ℝ) * Δt)
  simp only [add_zero, hshift] at key
  rw [LinearSys.stepInput, hsplit]
  exact key.symm

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
