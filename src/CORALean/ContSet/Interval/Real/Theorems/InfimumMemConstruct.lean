import CORALean.ContSet.Interval.Real.Operations.Infimum
import CORALean.ContSet.Interval.Real.Operations.IsNonempty

/-!
# The infimum of a nonempty interval lies in it

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

theorem Interval.infimum_mem_construct (I : Interval α) (h : I.IsNonempty) :
    I.infimum ∈ I.construct := fun i => ⟨le_rfl, h i⟩

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
