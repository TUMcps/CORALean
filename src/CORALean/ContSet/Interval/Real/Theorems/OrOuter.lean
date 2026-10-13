import CORALean.ContSet.Interval.Real.Operations.Or

/-!
# `Interval.or` contains the union

Unconditional: each operand lies inside the coordinatewise hull whether or not the other is empty.
Where CORA returns the other operand for an empty one, this returns the hull of both, which is
coarser, so the statement is an enclosure and never an equality.
-/

-- Authors:       Claude Opus 5.5
-- Written:       01-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Entrywise

variable {α ι : Type} [AddCommGroup α] [Module ℝ α] [Entrywise α ι]


-- =======================================  MAIN THEOREM  ======================================= --

theorem Interval.or_outer (I₁ I₂ : Interval α) :
    I₁.construct ∪ I₂.construct ⊆ (I₁.or I₂).construct := by -- --- PROOF ---
  rintro x (hx | hx) i
  · simp only [Interval.or, Entrywise.entry_ofEntry]
    exact ⟨le_trans (min_le_left _ _) (hx i).1, le_trans (hx i).2 (le_max_left _ _)⟩
  · simp only [Interval.or, Entrywise.entry_ofEntry]
    exact ⟨le_trans (min_le_right _ _) (hx i).1, le_trans (hx i).2 (le_max_right _ _)⟩

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
