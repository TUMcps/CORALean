import CORALean.ContSet.Interval.Real.Theorems.IsNonempty

/-!
# Crossed bounds denote the empty set

The negation of `isNonempty_iff`, stated because that is the direction the
degenerate case is used in: an interval whose lower bound exceeds its upper one
is not a small box but no box at all.
-/

-- Authors:       Tobias Ladner
-- Written:       17-August-2026
-- Last update:   04-September-2026
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α ι : Type} [AddCommGroup α] [Module ℝ α] [Entrywise α ι]


-- =======================================  MAIN THEOREM  ======================================= --

theorem Interval.not_isNonempty_iff (I : Interval α) : ¬I.IsNonempty ↔ I.construct = ∅ := by
  rw [Interval.isNonempty_iff, Set.not_nonempty_iff_eq_empty]

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
