import CORALean.Real.ContSet.Interval.Operations.LinComb

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

variable {n : ℕ}

theorem Interval.linComb_outer (I₁ I₂ : Interval n) :
    segments I₁.construct I₂.construct ⊆ (I₁.linComb I₂).construct := by
  rintro x ⟨y₁, h₁, y₂, h₂, lam, ⟨hl0, hl1⟩, rfl⟩
  intro i
  have a1 := h₁ i
  have a2 := h₂ i
  constructor
  · show min (I₁.inf i) (I₂.inf i) ≤ lam * y₁ i + (1 - lam) * y₂ i
    have hm1 : min (I₁.inf i) (I₂.inf i) ≤ y₁ i := le_trans (min_le_left _ _) a1.1
    have hm2 : min (I₁.inf i) (I₂.inf i) ≤ y₂ i := le_trans (min_le_right _ _) a2.1
    nlinarith
  · show lam * y₁ i + (1 - lam) * y₂ i ≤ max (I₁.sup i) (I₂.sup i)
    have hm1 : y₁ i ≤ max (I₁.sup i) (I₂.sup i) := le_trans a1.2 (le_max_left _ _)
    have hm2 : y₂ i ≤ max (I₁.sup i) (I₂.sup i) := le_trans a2.2 (le_max_right _ _)
    nlinarith

end CORALean.Real
