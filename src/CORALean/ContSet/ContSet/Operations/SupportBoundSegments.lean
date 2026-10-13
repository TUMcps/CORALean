import CORALean.ContSet.ContSet.ContSet
import CORALean.Global.LinProg.LinProg
import Mathlib.Tactic.Linarith

/-!
# The support bound across `segments`

`Global.LinProg.Composition` carries a bound across the operations Mathlib
names. `segments` is ours — CORA's `linComb`, which is the convex hull only when
both sets already are — so its case belongs here, computing the combined bound
rather than beside the definition.
-/

-- Authors:       Claude Sonnet 5
-- Written:       02-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

variable {α : Type} [AddCommGroup α] [Module ℝ α] {S T : Set α} {c : α →ₗ[ℝ] ℝ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- A point between the two sets is a weighted average of one from each, so
neither bound is beaten. -/
def SupportBound.segments (u : SupportBound S c) (v : SupportBound T c) :
    SupportBound (segments S T) c where
  val := max u.val v.val
  le := by
    rintro _ ⟨y₁, h₁, y₂, h₂, lam, ⟨hl₀, hl₁⟩, rfl⟩
    show c (lam • y₁ + (1 - lam) • y₂) ≤ max u.val v.val
    rw [map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul]
    have b₁ := le_trans (u.le y₁ h₁) (le_max_left u.val v.val)
    have b₂ := le_trans (v.le y₂ h₂) (le_max_right u.val v.val)
    calc lam * c y₁ + (1 - lam) * c y₂
        ≤ lam * max u.val v.val + (1 - lam) * max u.val v.val :=
          add_le_add (mul_le_mul_of_nonneg_left b₁ hl₀)
            (mul_le_mul_of_nonneg_left b₂ (by linarith))
      _ = max u.val v.val := by ring

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
