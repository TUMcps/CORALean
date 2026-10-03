import CORALean.ContSet.Fullspace.Real.Operations.IsBounded
import CORALean.ContSet.Fullspace.Real.Theorems.IsBoundedConstructIff

/-!
# `Fullspace.isBounded` is boundedness

The `Bool` `Fullspace.isBounded` is `true` exactly when the set is bounded: exact.
-/

-- Authors:       Tobias Ladner
-- Written:       03-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Fullspace.isBounded_iff (F : Fullspace n) :
    F.isBounded = true ↔ Bornology.IsBounded F.construct := by
  simpa [Fullspace.isBounded] using (Fullspace.isBounded_construct_iff F).symm

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
