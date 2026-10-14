module

public import CORALean.ContSet.Interval.Real.Operations.Basic

@[expose] public section

/-!
# `Interval.abs_sub_center_le`

What makes `center` and `radius` a genuine split of a box's point rather than
two unrelated readings: every point the box denotes is off from the centre by
at most the radius, coordinate by coordinate — how every enclosure proof off a
box reads it.
-/

-- Authors:       Claude Opus 5
-- Written:       04-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Entrywise

variable {α ι : Type} [AddCommGroup α] [Module ℝ α] [Entrywise α ι]


-- =======================================  MAIN THEOREM  ======================================= --

/-- A point the box denotes is the centre off by at most the radius, which is
how every enclosure proof splits it. -/
theorem Interval.abs_sub_center_le {I : Interval α} {x : α} (hx : x ∈ I.construct) (i : ι) :
    |entry x i - entry I.center i| ≤ entry I.radius i := by
  have h := hx i
  rw [Interval.center, Interval.radius, entry_smul, entry_smul, entry_add, entry_sub, abs_le]
  constructor <;> linarith [h.1, h.2]

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
