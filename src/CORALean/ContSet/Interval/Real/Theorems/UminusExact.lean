module

public import CORALean.ContSet.Interval.Real.Operations.Basic

@[expose] public section

/-!
# `Interval.uminus` is exactly the negated set

Coordinatewise. Needs no nonemptiness: a crossed box negates to a crossed box.

## Inputs
* `I` – interval

## Hypotheses
* none

## Conclusion
* the negated box represents exactly the negated set
-/

-- Authors:       Claude Opus 5.5
-- Written:       01-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Pointwise Entrywise

variable {α ι : Type} [AddCommGroup α] [Module ℝ α] [Entrywise α ι]


-- =======================================  MAIN THEOREM  ======================================= --

theorem Interval.uminus_exact (I : Interval α) :
    -I.construct = I.uminus.construct := by -- --- PROOF ---
  ext x
  constructor
  · intro hx i
    have h := hx i
    rw [Entrywise.entry_neg] at h
    exact ⟨by rw [show I.uminus.inf = -I.sup from rfl, Entrywise.entry_neg]; linarith [h.2],
      by rw [show I.uminus.sup = -I.inf from rfl, Entrywise.entry_neg]; linarith [h.1]⟩
  · intro hx i
    have h := hx i
    rw [show I.uminus.inf = -I.sup from rfl, Entrywise.entry_neg] at h
    rw [show I.uminus.sup = -I.inf from rfl, Entrywise.entry_neg] at h
    show _ ∧ _
    rw [Entrywise.entry_neg]
    exact ⟨by linarith [h.2], by linarith [h.1]⟩

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
