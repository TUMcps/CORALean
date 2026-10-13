module

public import CORALean.ContSet.EmptySet.Real.Operations.Not
public import CORALean.ContSet.EmptySet.Real.Instances
public import CORALean.ContSet.Fullspace.Real.Instances

@[expose] public section

/-!
# `EmptySet.not` is the complement
-/

-- Authors:       Claude Opus 5.5
-- Written:       01-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open ContSet

variable {n m : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem EmptySet.not_exact (E : EmptySet n) : E.not.construct = (E.construct)ᶜ := by
  change (Set.univ : Set (Vec ℝ n)) = (∅ : Set (Vec ℝ n))ᶜ
  exact Set.compl_empty.symm

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
