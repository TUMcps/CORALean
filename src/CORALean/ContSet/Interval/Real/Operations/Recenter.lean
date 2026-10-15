module

public import CORALean.ContSet.Interval.Real.Operations.Basic

@[expose] public section

/-!
# `Interval.recenter`

Both bounds shifted by the center: the box moved to hold the origin exactly
where its center sat. `Theorems/RecenterZeroMem.lean` needs the box nonempty
to say the origin is still inside; `Instances.lean`'s docstring says why that
keeps `Recenter` itself unavailable.
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

noncomputable def Interval.recenter (I : Interval α) : Interval α :=
  ⟨I.inf - I.center, I.sup - I.center⟩

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
