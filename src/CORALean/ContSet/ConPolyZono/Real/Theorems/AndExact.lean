import CORALean.ContSet.ConPolyZono.Real.Theorems.AndDepExact
import CORALean.ContSet.ConPolyZono.Real.Theorems.DependentExact

/-!
# `ConPolyZono.and` is exactly the intersection

The claim the representation exists for, and the one no convex representation
here can make without giving something away.

`andDep_exact` at the zero-width box does the work; `dependent_exact` empties
the independent blocks it asks for, and empties them costlessly.
-/

-- Authors:       Tobias Ladner
-- Written:       02-September-2026
-- Last update:   04-September-2026
-- Last revision: ---

namespace CORALean.Real

open Pointwise

variable {n : ℕ}

/-- Translating by the zero-width box is doing nothing, which is what makes
`andDep_exact` at that tolerance the intersection. -/
theorem ConPolyZono.aux_add_point_zero (S : Set (Vec ℝ n)) :
    S + (Interval.point (0 : Vec ℝ n)).construct = S := by
  have hzero : ∀ z : Vec ℝ n, z ∈ (Interval.point (0 : Vec ℝ n)).construct → z = 0 := by
    intro z hz
    funext i
    have h : (0:ℝ) ≤ z i ∧ z i ≤ 0 := hz i
    show z i = 0
    linarith [h.1, h.2]
  -- both directions, the only member of a zero-width box being `0`
  ext x
  constructor
  · rintro ⟨y, hy, z, hz, hyz⟩
    have h : y + z = x := hyz
    rw [hzero z hz, add_zero] at h
    rw [← h]
    exact hy
  · intro hx
    exact ⟨x, hx, 0, Interval.mem_point 0, add_zero x⟩

theorem ConPolyZono.and_exact (C₁ C₂ : ConPolyZono (Vec ℝ n)) :
    C₁.construct ∩ C₂.construct = (C₁.and C₂).construct := by
  rw [C₁.dependent_exact, C₂.dependent_exact,
    ← ConPolyZono.aux_add_point_zero C₂.dependent.construct]
  exact ConPolyZono.andDep_exact C₁.dependent C₂.dependent _ rfl rfl

end CORALean.Real
