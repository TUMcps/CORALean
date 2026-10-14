module

public import CORALean.ContSet.ContSet.ContSet
public import Mathlib.Analysis.Convex.Join
public import Mathlib.Tactic.Linarith

@[expose] public section

/-!
# `Set.linComb` is Mathlib's convex join

The parameter runs over `[0,1]` either way, one written as `λ` and the other as `1 - λ`.
-/

-- Authors:       Claude Opus 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

variable {α : Type} [AddCommGroup α] [Module ℝ α]


-- =======================================  MAIN THEOREM  ======================================= --

theorem setLinComb_eq_convexJoin (X Y : Set α) :
    Set.linComb X Y = convexJoin ℝ X Y := by -- --- PROOF ---
  ext x
  simp only [Set.linComb, Set.mem_setOf_eq, mem_convexJoin, segment_eq_image, Set.mem_image,
    Set.mem_Icc]
  constructor
  · rintro ⟨y₁, h₁, y₂, h₂, lam, ⟨hl₀, hl₁⟩, rfl⟩
    exact ⟨y₁, h₁, y₂, h₂, 1 - lam, ⟨by linarith, by linarith⟩, by rw [sub_sub_cancel]⟩
  · rintro ⟨y₁, h₁, y₂, h₂, θ, ⟨h₀, h₁'⟩, rfl⟩
    exact ⟨y₁, h₁, y₂, h₂, 1 - θ, ⟨by linarith, by linarith⟩, by rw [sub_sub_cancel]⟩

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
