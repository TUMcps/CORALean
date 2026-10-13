module

public import CORALean.ContDynamics.LinearSys.Theorems.StepInputEqShifted

@[expose] public section

/-!
# One step of the input, re-anchored at any other step

`stepInput_shift` reads `stepInput_eq_shifted` the other way — step `0` of a
signal re-anchored at `kΔt` *is* step `k` of the original. That is what lets a
loop that re-anchors the trajectory at every step state its input hypothesis in
the original clock while each step is proved on a clock starting at zero.
-/

-- Authors:       Claude Opus 5
-- Written:       02-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

variable {n : ℕ} {𝕋 : Type} [Scalar 𝕋]


-- =======================================  MAIN THEOREM  ======================================= --

/-- Step `0` of the signal re-anchored at `kΔt` is step `k` of the original. -/
theorem LinearSys.stepInput_shift (sys : LinearSys 𝕋 n) (u : ℝ → Vec ℝ n) (Δt : ℝ) (k : ℕ) :
    sys.stepInput (fun t => u ((k : ℝ) * Δt + t)) Δt 0 = sys.stepInput u Δt k := by
  rw [sys.stepInput_eq_shifted (fun t => u ((k : ℝ) * Δt + t)) Δt 0,
    sys.stepInput_eq_shifted u Δt k]
  simp only [Nat.cast_zero, zero_mul, zero_add]

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
