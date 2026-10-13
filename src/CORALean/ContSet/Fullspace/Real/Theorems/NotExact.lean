import CORALean.ContSet.Fullspace.Real.Operations.Not
import CORALean.ContSet.EmptySet.Real.EmptySet

/-!
# `Fullspace.not` is the complement
-/

-- Authors:       Claude Opus 5.5
-- Written:       01-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n m : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Fullspace.not_exact (F : Fullspace n) : F.not.construct = (F.construct)ᶜ := by
  change (∅ : Set (Vec ℝ n)) = (Set.univ : Set (Vec ℝ n))ᶜ
  exact Set.compl_univ.symm

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
