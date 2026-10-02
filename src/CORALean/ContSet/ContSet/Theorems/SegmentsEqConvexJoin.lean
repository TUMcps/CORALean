import CORALean.ContSet.ContSet.ContSet
import Mathlib.Analysis.Convex.Join
import Mathlib.Tactic.Linarith

/-!
# `segments` is Mathlib's convex join

The parameter runs over `[0,1]` either way, one written as `λ` and the other as `1 - λ`.
-/

-- Authors:       Tobias Ladner
-- Written:       02-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

variable {α : Type} [AddCommGroup α] [Module ℝ α]


-- =======================================  MAIN THEOREM  ======================================= --

theorem segments_eq_convexJoin (X Y : Set α) :
    segments X Y = convexJoin ℝ X Y := by -- --- PROOF ---
  ext x
  simp only [segments, Set.mem_setOf_eq, mem_convexJoin, segment_eq_image, Set.mem_image,
    Set.mem_Icc]
  constructor
  · rintro ⟨y₁, h₁, y₂, h₂, lam, ⟨hl₀, hl₁⟩, rfl⟩
    exact ⟨y₁, h₁, y₂, h₂, 1 - lam, ⟨by linarith, by linarith⟩, by rw [sub_sub_cancel]⟩
  · rintro ⟨y₁, h₁, y₂, h₂, θ, ⟨h₀, h₁'⟩, rfl⟩
    exact ⟨y₁, h₁, y₂, h₂, 1 - θ, ⟨by linarith, by linarith⟩, by rw [sub_sub_cancel]⟩

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
