module

public import CORALean.ContSet.Taylm.Real.Operations.ListMax
public import Mathlib.Order.MinMax

@[expose] public section

/-!
# The greatest value is at least every value
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =======================================  MAIN THEOREM  ======================================= --

theorem Taylm.le_listMax {α : Type} (f : α → ℝ) : ∀ {l : List α} {a : α}, a ∈ l →
    f a ≤ Taylm.listMax f l
  | [], _, h => by simp at h
  | [b], a, h => by simp at h; subst h; simp [Taylm.listMax]
  | b :: c :: l, a, h => by
    rcases List.mem_cons.1 h with rfl | h
    · exact le_max_left _ _
    · exact le_trans (Taylm.le_listMax f h) (le_max_right _ _)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
