import CORALean.ContSet.SpectraShadow.Real.Theorems.SupportFuncNeTopIff

/-!
# `SpectraShadow.supportFunc_eq_top_of_unbounded`

A direction in which the functional exceeds every real number on the set gives `⊤`.
-/

-- Authors:       Tobias Ladner
-- Written:       04-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix

variable {α : Type} [AddCommGroup α] [Module ℝ α]


-- =======================================  MAIN THEOREM  ======================================= --

theorem SpectraShadow.supportFunc_eq_top_of_unbounded (S : SpectraShadow α) (c : α →ₗ[ℝ] ℝ)
    (h : ∀ M : ℝ, ∃ x ∈ S.construct, M < c x) : S.supportFunc c = ⊤ := by
  by_contra hne
  obtain ⟨M, hM⟩ := (S.supportFunc_ne_top_iff c).mp hne
  obtain ⟨x, hx, hlt⟩ := h M
  exact absurd (hM x hx) (not_le.mpr hlt)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
