import CORALean.ContSet.Interval.Real.Operations.Empty
import CORALean.ContSet.Interval.Real.Theorems.NotIsNonempty

/-!
# `Interval.empty` denotes the empty set

For `0 < n`: in dimension `0` there is a single point, and a box with no coordinates contains it.
-/

-- Authors:       Tobias Ladner
-- Written:       01-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Interval.empty_exact (hn : 0 < n) : (Interval.empty n).construct = ∅ := by
  rw [← Interval.not_isNonempty_iff]
  intro h
  have h0 : (1 : ℝ) ≤ 0 := h ⟨0, hn⟩
  linarith


end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
