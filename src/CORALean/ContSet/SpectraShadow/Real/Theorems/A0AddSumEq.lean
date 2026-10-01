import CORALean.ContSet.SpectraShadow.Real.SpectraShadow

/-!
# The inequality of a spectrahedral shadow with zero `Aᵢ`

With every `Aᵢ` zero, the inequality does not depend on the coefficients.
-/

-- Authors:       Tobias Ladner
-- Written:       01-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =======================================  MAIN THEOREM  ======================================= --

theorem SpectraShadow.A₀_add_sum_eq {α : Type} [AddCommGroup α] [Module ℝ α] (S : SpectraShadow α)
    (β : Fin S.m → ℝ) (h : ∀ i, S.A i = 0) : S.A₀ + ∑ i, β i • S.A i = S.A₀ := by
  simp [h]

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
