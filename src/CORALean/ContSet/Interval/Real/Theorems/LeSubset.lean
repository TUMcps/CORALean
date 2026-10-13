import CORALean.ContSet.Interval.Real.Operations.Le

/-!
# `Interval.le` implies containment

Chaining the bounds, coordinate by coordinate. Needs no nonemptiness: an empty `I` is contained in
everything.
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

theorem Interval.le_subset {I J : Interval α} (h : I.le J) :
    I.construct ⊆ J.construct := by
  intro x hx i
  exact ⟨le_trans (h i).1 (hx i).1, le_trans (hx i).2 (h i).2⟩


end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
