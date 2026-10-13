import CORALean.ContSet.HPolytope.Real.Operations.Fullspace

/-!
# `HPolytope.fullspace` denotes `Set.univ`

There is no row index to discharge, in either block, so the set it denotes is
one `ext` away.
-/

-- Authors:       Claude Opus 5
-- Written:       04-September-2026
-- Last update:   05-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α : Type} [AddCommGroup α] [Module ℝ α]


-- =======================================  MAIN THEOREM  ======================================= --

-- there is no row index to discharge, in either block
theorem HPolytope.construct_fullspace : (HPolytope.fullspace α).construct = Set.univ := by
  ext x
  exact ⟨fun _ => trivial, fun _ => ⟨fun i => i.elim0, fun i => i.elim0⟩⟩

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
