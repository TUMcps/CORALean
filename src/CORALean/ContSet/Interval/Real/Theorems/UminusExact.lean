import CORALean.ContSet.Interval.Real.Operations.Uminus

/-!
# `Interval.uminus` is exactly the negated set

Coordinatewise. Needs no nonemptiness: a crossed box negates to a crossed box.
-/

-- Authors:       Tobias Ladner
-- Written:       01-October-2026
-- Last update:   ---
-- Last revision: ---


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
