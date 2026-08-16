import CORALean.ContSet.Interval.API

/-!
# `Interval.plus` over-approximates the Minkowski sum

Coordinatewise. The inclusion is an equality, but only this direction is
recorded.
-/

-- Authors:       Tobias Ladner
-- Written:       16-August-2026
-- Last update:   ---
-- Last revision: ---

namespace CORALean.Interval.Proofs

open Pointwise

variable {n : ℕ}

theorem plus_sound (I₁ I₂ : Interval n) :
    I₁.construct + I₂.construct ⊆ (I₁.plus I₂).construct := by
  rintro _ ⟨x₁, hx₁, x₂, hx₂, rfl⟩ i
  exact ⟨add_le_add (hx₁ i).1 (hx₂ i).1, add_le_add (hx₁ i).2 (hx₂ i).2⟩

end CORALean.Interval.Proofs
