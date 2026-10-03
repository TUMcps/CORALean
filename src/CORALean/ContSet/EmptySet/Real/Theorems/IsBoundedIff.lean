import CORALean.ContSet.EmptySet.Real.Operations.IsBounded
import CORALean.ContSet.EmptySet.Real.Instances

/-!
# `EmptySet.isBounded` is boundedness

The `Bool` `EmptySet.isBounded` is `true` exactly when the set is bounded: exact.
-/

-- Authors:       Tobias Ladner
-- Written:       03-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem EmptySet.isBounded_iff (F : EmptySet n) :
    F.isBounded = true ↔ Bornology.IsBounded F.construct := by
  simp [EmptySet.isBounded, EmptySet.construct]

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
