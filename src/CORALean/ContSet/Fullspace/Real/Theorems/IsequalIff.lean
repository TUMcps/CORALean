import CORALean.ContSet.Fullspace.Real.Operations.Isequal

/-!
# `Fullspace.isequal` decides equality of the denotations

Both denote the whole space, so `true` is the right answer, and it is the answer exactly when
the sets are equal.
-/

-- Authors:       Tobias Ladner
-- Written:       02-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n m : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Fullspace.isequal_iff (E F : Fullspace n) :
    E.isequal F = true ↔ E.construct = F.construct :=
  ⟨fun _ => rfl, fun _ => rfl⟩

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
