import CORALean.ContSet.Fullspace.Real.Operations.And
import CORALean.ContSet.ContSet.ContSet

/-!
# `Fullspace.and_` is exact

Intersecting the full space with a set of any representation gives that set.
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

theorem Fullspace.and_exact {S : Type} [ContSet S (Vec ℝ n)] (F : Fullspace n) (s : S) :
    ContSet.construct (F.and_ s) = F.construct ∩ ContSet.construct s := by
  change ContSet.construct s = Set.univ ∩ ContSet.construct s
  exact (Set.univ_inter _).symm

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
