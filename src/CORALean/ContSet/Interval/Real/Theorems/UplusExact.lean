import CORALean.ContSet.Interval.Real.Operations.Uplus

/-!
# `Interval.uplus` is the identity

The set is unchanged, definitionally.
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

theorem Interval.uplus_exact (I : Interval α) : I.uplus.construct = I.construct := rfl

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
