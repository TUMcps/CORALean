import CORALean.ContSet.SpectraShadow.Real.SpectraShadow

/-!
# `SpectraShadow.trace_lmi_mul`

The trace of the inequality's matrix against `Y` splits into one trace per coefficient matrix:
the other half of weak duality for `SpectraShadow`.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix

variable {α : Type} [AddCommGroup α] [Module ℝ α]


-- =======================================  MAIN THEOREM  ======================================= --

omit [AddCommGroup α] [Module ℝ α] in
theorem SpectraShadow.trace_lmi_mul (S : SpectraShadow α) (β : Fin S.m → ℝ) (Y : Mat ℝ S.k S.k) :
    ((S.A₀ + ∑ i, β i • S.A i) * Y).trace
      = (S.A₀ * Y).trace + ∑ i, β i * (S.A i * Y).trace := by
  rw [Matrix.add_mul, Matrix.trace_add, Matrix.sum_mul, Matrix.trace_sum]
  simp only [Matrix.smul_mul, Matrix.trace_smul, smul_eq_mul]

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
