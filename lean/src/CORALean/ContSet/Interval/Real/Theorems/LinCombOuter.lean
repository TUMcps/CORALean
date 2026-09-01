import CORALean.ContSet.Interval.Real.Operations.LinComb

/-!
# `linComb` contains every segment between the two intervals

A weighted average of two numbers never leaves the range spanned by both, so
each coordinate is handled on its own and the bound is immediate.
-/

-- Authors:       Tobias Ladner
-- Written:       18-August-2026
-- Last update:   ---
-- Last revision: ---

namespace CORALean.Real

open Entrywise

variable {α ι : Type} [AddCommGroup α] [Module ℝ α] [Entrywise α ι]

theorem Interval.linComb_outer (I₁ I₂ : Interval α) :
    segments I₁.construct I₂.construct ⊆ (I₁.linComb I₂).construct := by
  rintro x ⟨y₁, h₁, y₂, h₂, lam, ⟨hl0, hl1⟩, rfl⟩
  intro i
  have a1 := h₁ i
  have a2 := h₂ i
  simp only [Interval.linComb, Entrywise.entry_ofEntry, Entrywise.entry_add,
    Entrywise.entry_smul]
  constructor
  · have hm1 : min (entry I₁.inf i) (entry I₂.inf i) ≤ entry y₁ i :=
      le_trans (min_le_left _ _) a1.1
    have hm2 : min (entry I₁.inf i) (entry I₂.inf i) ≤ entry y₂ i :=
      le_trans (min_le_right _ _) a2.1
    nlinarith
  · have hm1 : entry y₁ i ≤ max (entry I₁.sup i) (entry I₂.sup i) :=
      le_trans a1.2 (le_max_left _ _)
    have hm2 : entry y₂ i ≤ max (entry I₁.sup i) (entry I₂.sup i) :=
      le_trans a2.2 (le_max_right _ _)
    nlinarith

end CORALean.Real
