import CORALean.ContSet.Interval.Real.Operations.Supremum
import CORALean.ContSet.Interval.Real.Operations.IsNonempty

/-!
# The supremum of a nonempty interval lies in it

Nonempty only: for crossed bounds the set is `∅`.
-/

-- Authors:       Claude Opus 5.5
-- Written:       01-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Entrywise

variable {α ι : Type} [AddCommGroup α] [Module ℝ α] [Entrywise α ι]


-- =======================================  MAIN THEOREM  ======================================= --

theorem Interval.supremum_mem_construct (I : Interval α) (h : I.IsNonempty) :
    I.supremum ∈ I.construct := fun i => ⟨h i, le_rfl⟩

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
