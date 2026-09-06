import CORALean.ContSet.Interval.Real.Operations.Recentre
import CORALean.ContSet.Interval.Real.Theorems.MemCenter

/-!
# The recentred box contains the origin, if the box was nonempty

Read straight off `Interval.mem_center`: the centre sitting between the
original bounds is exactly what puts `0` between the shifted ones. A crossed
box has no centre inside it, so this carries no hypothesis beyond that one.
-/

-- Authors:       Tobias Ladner
-- Written:       06-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Entrywise

variable {α ι : Type} [AddCommGroup α] [Module ℝ α] [Entrywise α ι]


-- =======================================  MAIN THEOREM  ======================================= --

theorem Interval.zero_mem_recentre (I : Interval α) (hI : I.IsNonempty (ι := ι)) :
    (0 : α) ∈ (I.recentre).construct := fun i => by
  have h := I.mem_center hI i
  show entry (I.inf - I.center) i ≤ entry (0 : α) i ∧
    entry (0 : α) i ≤ entry (I.sup - I.center) i
  rw [entry_sub, entry_sub, entry_zero]
  exact ⟨by linarith [h.1], by linarith [h.2]⟩

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
