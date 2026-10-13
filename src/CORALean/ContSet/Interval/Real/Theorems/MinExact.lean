import CORALean.ContSet.Interval.Real.Operations.Min
import CORALean.ContSet.Interval.Real.Operations.IsNonempty

/-!
# `Interval.min` is exactly the set of entrywise minima

The counterpart of `Interval.max_exact`. Nonemptiness of both operands is needed for the same
reason: an empty operand has no minima to fill the box.
-/

-- Authors:       Claude Opus 5.5
-- Written:       01-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Entrywise

variable {α ι : Type} [AddCommGroup α] [Module ℝ α] [Entrywise α ι]


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

theorem aux_min_exists {a₁ b₁ a₂ b₂ z : ℝ} (h₁ : a₁ ≤ b₁) (h₂ : a₂ ≤ b₂)
    (hl : Min.min a₁ a₂ ≤ z) (hu : z ≤ Min.min b₁ b₂) :
    ∃ x y : ℝ, (a₁ ≤ x ∧ x ≤ b₁) ∧ (a₂ ≤ y ∧ y ≤ b₂) ∧ Min.min x y = z := by -- --- PROOF ---
  have hb₁ : z ≤ b₁ := le_trans hu (min_le_left _ _)
  have hb₂ : z ≤ b₂ := le_trans hu (min_le_right _ _)
  by_cases hz : a₁ ≤ z
  · exact ⟨z, b₂, ⟨hz, hb₁⟩, ⟨h₂, le_refl _⟩, min_eq_left hb₂⟩
  · have hz₂ : a₂ ≤ z := by
      rcases min_cases a₁ a₂ with ⟨h, _⟩ | ⟨h, _⟩ <;> rw [h] at hl
      · exact absurd hl hz
      · exact hl
    exact ⟨b₁, z, ⟨h₁, le_refl _⟩, ⟨hz₂, hb₂⟩, min_eq_right hb₁⟩


-- =======================================  MAIN THEOREM  ======================================= --

theorem Interval.min_exact {I₁ I₂ : Interval α} (h₁ : I₁.IsNonempty) (h₂ : I₂.IsNonempty) :
    (I₁.min I₂).construct = Set.image2
      (fun x y : α => (ofEntry fun i => Min.min (entry x i) (entry y i) : α))
      I₁.construct I₂.construct := by -- --- PROOF ---
  ext z
  constructor
  · intro hz
    have key : ∀ i, ∃ x y : ℝ, (entry I₁.inf i ≤ x ∧ x ≤ entry I₁.sup i) ∧
        (entry I₂.inf i ≤ y ∧ y ≤ entry I₂.sup i) ∧ Min.min x y = entry z i := fun i => by
      have h := hz i
      simp only [Interval.min, entry_ofEntry] at h
      exact aux_min_exists (h₁ i) (h₂ i) h.1 h.2
    choose x y hx hy hxy using key
    refine ⟨ofEntry x, fun i => ?_, ofEntry y, fun i => ?_, Entrywise.ext fun i => ?_⟩
    · simpa using hx i
    · simpa using hy i
    · simpa using hxy i
  · rintro ⟨x, hx, y, hy, rfl⟩ i
    simp only [Interval.min, entry_ofEntry]
    exact ⟨min_le_min (hx i).1 (hy i).1, min_le_min (hx i).2 (hy i).2⟩

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
