module

public import CORALean.ContSet.Interval.Real.Operations.Recenter
public import CORALean.ContSet.Interval.Real.Theorems.MemCenter

@[expose] public section

/-!
# The recentered box contains the origin, if the box was nonempty

Read straight off `Interval.mem_center`: the center sitting between the
original bounds is exactly what puts `0` between the shifted ones. A crossed
box has no center inside it, so this carries no hypothesis beyond that one.

## Inputs
* `I` – interval

## Hypotheses
* `hI` – interval nonempty

## Conclusion
* the origin lies in the recentered interval
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

theorem Interval.zero_mem_recenter (I : Interval α) (hI : I.IsNonempty (ι := ι)) :
    (0 : α) ∈ (I.recenter).construct := fun i => by
  have h := I.mem_center hI i
  show entry (I.inf - I.center) i ≤ entry (0 : α) i ∧
    entry (0 : α) i ≤ entry (I.sup - I.center) i
  rw [entry_sub, entry_sub, entry_zero]
  exact ⟨by linarith [h.1], by linarith [h.2]⟩

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
