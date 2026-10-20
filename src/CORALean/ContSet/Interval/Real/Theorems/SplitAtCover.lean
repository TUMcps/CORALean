module

public import CORALean.ContSet.Interval.Real.Operations.SplitAt

@[expose] public section

/-!
# `Interval.splitAt` covers the box it bisects

A cover, not a partition: the two halves share the slice at the midpoint of
coordinate `j`, so this is `⊆`, not `=`. No `IsNonempty` is needed — an empty
box is covered by two empty boxes just as well, `le_total` alone deciding
which half a point's `j`-th coordinate falls into.

## Inputs
* `I` – interval
* `j` – entry to split at

## Hypotheses
* none

## Conclusion
* the two halves together cover the interval
-/

-- Authors:       Claude Opus 5
-- Written:       06-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Entrywise

variable {α ι : Type} [AddCommGroup α] [Module ℝ α] [Entrywise α ι] [DecidableEq ι]


-- =======================================  MAIN THEOREM  ======================================= --

theorem Interval.splitAt_cover (I : Interval α) (j : ι) :
    I.construct ⊆ (I.splitAt j).1.construct ∪ (I.splitAt j).2.construct := by -- --- PROOF ---
  intro x hx
  unfold Interval.splitAt
  rcases le_total (entry x j) (entry I.center j) with h | h
  · refine Or.inl fun i => ⟨(hx i).1, ?_⟩
    by_cases hij : i = j
    · subst hij; rw [entry_ofEntry, Function.update_self]; exact h
    · rw [entry_ofEntry, Function.update_of_ne hij]; exact (hx i).2
  · refine Or.inr fun i => ⟨?_, (hx i).2⟩
    by_cases hij : i = j
    · subst hij; rw [entry_ofEntry, Function.update_self]; exact h
    · rw [entry_ofEntry, Function.update_of_ne hij]; exact (hx i).1

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
