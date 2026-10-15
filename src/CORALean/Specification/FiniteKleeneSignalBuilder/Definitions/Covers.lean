module

public import Mathlib.Data.EReal.Basic

@[expose] public section

/-!
# Where an interval marks a signal

`finiteSignal.indicator(dur,int,true)` with `int = interval(lo,hi)` is true at a time `t` of
`[0,dur]` exactly when the interval reaches into the signal (`0 < hi`, `lo < dur`) and `t` lies in
it, its right end being open unless it reaches the end `dur` of the signal, where the signal is
closed.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       15-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The interval `[lo,hi)` marks the time `t` of a signal of duration `dur`. -/
abbrev FiniteKleeneSignalBuilder.Covers (dur t : ℝ) (lo hi : EReal) : Prop :=
  0 < hi ∧ lo < (dur : EReal) ∧ lo ≤ (t : EReal) ∧ ((t : EReal) < hi ∨ (dur : EReal) ≤ hi)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
