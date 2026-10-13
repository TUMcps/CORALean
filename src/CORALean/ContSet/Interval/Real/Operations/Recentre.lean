import CORALean.ContSet.Interval.Real.Interval
import CORALean.ContSet.Interval.Real.Operations.Center

/-!
# `Interval.recentre`

Both bounds shifted by the centre: the box moved to hold the origin exactly
where its centre sat. `Theorems/RecentreZeroMem.lean` needs the box nonempty
to say the origin is still inside; `Instances.lean`'s docstring says why that
keeps `Recentre` itself unavailable.
-/

-- Authors:       Claude Opus 5
-- Written:       06-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Entrywise

variable {α ι : Type} [AddCommGroup α] [Module ℝ α] [Entrywise α ι]


-- =====================================  MAIN DEFINITION  ====================================== --

noncomputable def Interval.recentre (I : Interval α) : Interval α :=
  ⟨I.inf - I.center, I.sup - I.center⟩

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
