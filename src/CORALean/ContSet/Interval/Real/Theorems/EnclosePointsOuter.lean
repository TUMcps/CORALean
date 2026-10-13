module

public import CORALean.ContSet.Interval.Real.Operations.EnclosePoints

@[expose] public section

/-!
# `Interval.enclosePoints` contains every point

Each coordinate is bounded by the family's minimum and maximum there. Both bounds are attained, so
the box is the smallest one, but only containment is stated.
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

theorem Interval.enclosePoints_outer {κ : Type} [Fintype κ] [Nonempty κ] (p : κ → α) (k : κ) :
    p k ∈ (Interval.enclosePoints p).construct := by
  intro i
  simp only [Interval.enclosePoints, Entrywise.entry_ofEntry]
  exact ⟨Finset.inf'_le (fun k => entry (p k) i) (Finset.mem_univ k),
    Finset.le_sup' (fun k => entry (p k) i) (Finset.mem_univ k)⟩

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
