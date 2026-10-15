module

public import CORALean.ContSet.Interval.Real.Operations.Recenter

@[expose] public section

/-!
# A member shifted by the center lies in the recentered box

Unconditional: a member witnesses the box is nonempty on its own, so unlike
`RecenterZeroMem` this needs no `IsNonempty` hypothesis at all.
-/

-- Authors:       Claude Opus 5
-- Written:       06-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Entrywise

variable {α ι : Type} [AddCommGroup α] [Module ℝ α] [Entrywise α ι]


-- =======================================  MAIN THEOREM  ======================================= --

theorem Interval.sub_center_mem_recenter {I : Interval α} {y : α} (hy : y ∈ I.construct) :
    y - I.center ∈ (I.recenter).construct := fun i => by
  have h := hy i
  show entry (I.inf - I.center) i ≤ entry (y - I.center) i ∧
    entry (y - I.center) i ≤ entry (I.sup - I.center) i
  rw [entry_sub, entry_sub, entry_sub]
  exact ⟨by linarith [h.1], by linarith [h.2]⟩

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
