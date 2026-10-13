import CORALean.ContSet.SpectraShadow.Real.SpectraShadow

/-!
# `SpectraShadow.lmi_of_A_zero`

Variables on zero coefficient matrices do not enter the inequality.
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
theorem SpectraShadow.lmi_of_A_zero (S : SpectraShadow α) (β : Fin S.m → ℝ)
    (h : ∀ i, β i = 0 ∨ S.A i = 0) : S.A₀ + ∑ i, β i • S.A i = S.A₀ := by
  rw [Finset.sum_eq_zero fun i _ => by rcases h i with h | h <;> simp [h], add_zero]

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
