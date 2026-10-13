module

public import CORALean.ContSet.Fullspace.Real.Theorems.DisjointIff

@[expose] public section

/-!
# The full space meets a set iff it is nonempty


-/

-- Authors:       Claude Opus 5.5
-- Written:       01-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open ContSet

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Fullspace.not_disjoint_iff {S : Type} [ContSet S (Vec ℝ n)] (F : Fullspace n) (s : S) :
    ¬Disjoint (ContSet.construct s) F.construct ↔ (ContSet.construct s).Nonempty := by
  rw [Fullspace.disjoint_iff, Set.nonempty_iff_ne_empty]

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
