module

public import CORALean.ContSet.Taylm.Real.Operations.ListMin

@[expose] public section

/-!
# The least value is at most every value
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =======================================  MAIN THEOREM  ======================================= --

theorem Taylm.listMin_le {α : Type} (f : α → ℝ) : ∀ {l : List α} {a : α}, a ∈ l →
    Taylm.listMin f l ≤ f a
  | [], _, h => by simp at h
  | [b], a, h => by simp at h; subst h; simp [Taylm.listMin]
  | b :: c :: l, a, h => by
    rcases List.mem_cons.1 h with rfl | h
    · exact min_le_left _ _
    · exact le_trans (min_le_right _ _) (Taylm.listMin_le f h)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
