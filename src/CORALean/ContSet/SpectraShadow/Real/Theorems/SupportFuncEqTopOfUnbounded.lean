module

public import CORALean.ContSet.SpectraShadow.Real.Theorems.SupportFuncNeTopIff

@[expose] public section

/-!
# `SpectraShadow.supportFunc_eq_top_of_unbounded`

A direction in which the functional exceeds every real number on the set gives `⊤`.

## Inputs
* `S` – spectrahedral shadow
* `c` – linear functional

## Hypotheses
* `h` – `c` is unbounded above on `S`

## Conclusion
* the support function is `⊤`
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

theorem SpectraShadow.supportFunc_eq_top_of_unbounded (S : SpectraShadow α) (c : α →ₗ[ℝ] ℝ)
    (h : ∀ M : ℝ, ∃ x ∈ S.construct, M < c x) : S.supportFunc c = ⊤ := by
  by_contra hne
  obtain ⟨M, hM⟩ := (S.supportFunc_ne_top_iff c).mp hne
  obtain ⟨x, hx, hlt⟩ := h M
  exact absurd (hM x hx) (not_le.mpr hlt)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
