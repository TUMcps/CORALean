import CORALean.ContSet.EmptySet.Real.Operations.Centre
import CORALean.ContSet.EmptySet.Real.Instances

/-!
# `EmptySet.centre` is a point exactly when there is one

`∅` has a centre iff it has a point, and it has none.
-/

-- Authors:       Tobias Ladner
-- Written:       04-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

open ContSet in
theorem EmptySet.centre_isSome_iff (E : EmptySet n) :
    E.centre.isSome ↔ (construct E).Nonempty := by
  change (none : Option (Vec ℝ n)).isSome ↔ (∅ : Set (Vec ℝ n)).Nonempty
  simp

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
