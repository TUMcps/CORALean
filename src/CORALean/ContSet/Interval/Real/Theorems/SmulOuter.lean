import CORALean.ContSet.Interval.Real.Operations.Smul
import CORALean.ContSet.Interval.Real.Theorems.MulBetweenEndpoints

/-!
# `Interval.smul` over-approximates scaling every point of a box

Entrywise, `c • v`'s coordinate sits between the two scaled endpoints by
`mul_between_endpoints`, whichever way `c`'s sign swaps them; reading that back
through `Entrywise.entry_smul` is the rest.
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

theorem Interval.smul_outer (c : ℝ) (I : Interval α) {v : α} (hv : v ∈ I.construct) :
    c • v ∈ (Interval.smul c I).construct := by
  intro i
  simp only [Interval.smul, entry_ofEntry, entry_smul]
  exact Interval.mul_between_endpoints (hv i).1 (hv i).2

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
