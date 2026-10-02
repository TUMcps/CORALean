import CORALean.ContSet.EmptySet.Real.Operations.Isequal
import CORALean.ContSet.EmptySet.Real.Instances

/-!
# `EmptySet.isequal` decides equality of the denotations

Both denote `∅`, so `true` is the right answer, and it is the answer exactly when the sets
are equal.
-/

-- Authors:       Tobias Ladner
-- Written:       02-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n m : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

open ContSet in
theorem EmptySet.isequal_iff (E F : EmptySet n) :
    E.isequal F = true ↔ construct E = construct F :=
  ⟨fun _ => rfl, fun _ => rfl⟩

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
