module

public import CORALean.ContSet.Interval.Real.Operations.Max
public import CORALean.ContSet.Interval.Real.Operations.IsNonempty

@[expose] public section

/-!
# `Interval.max` is exactly the set of entrywise maxima

For two nonempty boxes, the points `max(x, y)` with `x` in the first and `y` in the second fill
`[max inf₁ inf₂, max sup₁ sup₂]` entirely: in each coordinate a target `z` between the two larger
bounds is `max` of a coordinate of each box (`aux_max_exists`). Nonemptiness is needed, for an
empty operand has no maxima to fill the box.
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

theorem aux_max_exists {a₁ b₁ a₂ b₂ z : ℝ} (h₁ : a₁ ≤ b₁) (h₂ : a₂ ≤ b₂)
    (hl : Max.max a₁ a₂ ≤ z) (hu : z ≤ Max.max b₁ b₂) :
    ∃ x y : ℝ, (a₁ ≤ x ∧ x ≤ b₁) ∧ (a₂ ≤ y ∧ y ≤ b₂) ∧ Max.max x y = z := by -- --- PROOF ---
  have ha₁ : a₁ ≤ z := le_trans (le_max_left _ _) hl
  have ha₂ : a₂ ≤ z := le_trans (le_max_right _ _) hl
  by_cases hz : z ≤ b₁
  · exact ⟨z, a₂, ⟨ha₁, hz⟩, ⟨le_refl _, h₂⟩, max_eq_left ha₂⟩
  · have hz₂ : z ≤ b₂ := by
      rcases max_cases b₁ b₂ with ⟨h, _⟩ | ⟨h, _⟩ <;> rw [h] at hu
      · exact absurd hu hz
      · exact hu
    exact ⟨a₁, z, ⟨le_refl _, h₁⟩, ⟨ha₂, hz₂⟩, max_eq_right ha₁⟩


-- =======================================  MAIN THEOREM  ======================================= --

theorem Interval.max_exact {I₁ I₂ : Interval α} (h₁ : I₁.IsNonempty) (h₂ : I₂.IsNonempty) :
    (I₁.max I₂).construct = Set.image2
      (fun x y : α => (ofEntry fun i => Max.max (entry x i) (entry y i) : α))
      I₁.construct I₂.construct := by -- --- PROOF ---
  ext z
  constructor
  · intro hz
    have key : ∀ i, ∃ x y : ℝ, (entry I₁.inf i ≤ x ∧ x ≤ entry I₁.sup i) ∧
        (entry I₂.inf i ≤ y ∧ y ≤ entry I₂.sup i) ∧ Max.max x y = entry z i := fun i => by
      have h := hz i
      simp only [Interval.max, entry_ofEntry] at h
      exact aux_max_exists (h₁ i) (h₂ i) h.1 h.2
    choose x y hx hy hxy using key
    refine ⟨ofEntry x, fun i => ?_, ofEntry y, fun i => ?_, Entrywise.ext fun i => ?_⟩
    · simpa using hx i
    · simpa using hy i
    · simpa using hxy i
  · rintro ⟨x, hx, y, hy, rfl⟩ i
    simp only [Interval.max, entry_ofEntry]
    exact ⟨max_le_max (hx i).1 (hy i).1, max_le_max (hx i).2 (hy i).2⟩

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
