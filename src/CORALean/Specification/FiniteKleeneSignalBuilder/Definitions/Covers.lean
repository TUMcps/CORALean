module

public import Mathlib.Data.Real.Basic

@[expose] public section

/-!
# Where an interval marks a signal

`finiteSignal.indicator(dur,int,true)` with `int = interval(lo,hi)` is true at a time `t` of
`[0,dur]` exactly when the interval reaches into the signal (`0 < hi`, `lo < dur`) and `t` lies in
it, its right end being open unless it reaches the end `dur` of the signal, where the signal is
closed.

## Inputs
* `dur` – signal duration
* `t` – time
* `lo` – interval lower bound
* `hi` – interval upper bound

## Output
* the interval marks the time
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       15-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The interval `[lo,hi)` marks the time `t` of a signal of duration `dur`. -/
abbrev FiniteKleeneSignalBuilder.Covers (dur t lo hi : ℝ) : Prop :=
  0 < hi ∧ lo < dur ∧ lo ≤ t ∧ (t < hi ∨ dur ≤ hi)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
