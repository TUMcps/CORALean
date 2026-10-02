import CORALean.ContSet.HPolytope.Real.Operations.EmptySet
import Mathlib.Tactic.Linarith

/-!
# `HPolytope.emptySet` denotes `∅`
-/

-- Authors:       Tobias Ladner
-- Written:       04-September-2026
-- Last update:   05-September-2026
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α : Type} [AddCommGroup α] [Module ℝ α]


-- =======================================  MAIN THEOREM  ======================================= --

theorem HPolytope.construct_emptySet : (HPolytope.emptySet α).construct = ∅ := by -- --- PROOF ---
  ext x
  simp only [Set.mem_empty_iff_false, iff_false]
  rintro ⟨hle, -⟩
  -- the row index ascribed at `Fin 1`, the count's reduced spelling
  have h : (0:ℝ) ≤ -1 := hle (0 : Fin 1)
  linarith

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
