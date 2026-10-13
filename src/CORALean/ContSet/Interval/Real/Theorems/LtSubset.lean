import CORALean.ContSet.Interval.Real.Operations.Lt
import CORALean.ContSet.Interval.Real.Theorems.LeSubset

/-!
# `Interval.lt` implies containment

Strict inequalities are inequalities, so `lt` gives `le` and then `le_subset`. One direction only:
containment can hold with faces touching, which `lt` excludes.
-/

-- Authors:       Claude Opus 5.5
-- Written:       01-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Entrywise

variable {α ι : Type} [AddCommGroup α] [Module ℝ α] [Entrywise α ι]


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

theorem aux_lt_le {I J : Interval α} (h : I.lt J) : I.le J :=
  fun i => ⟨(h i).1.le, (h i).2.le⟩


-- =======================================  MAIN THEOREM  ======================================= --

theorem Interval.lt_subset {I J : Interval α} (h : I.lt J) :
    I.construct ⊆ J.construct :=
  Interval.le_subset (aux_lt_le h)


end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
