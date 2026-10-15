module

public import CORALean.Specification.FiniteSignal.FiniteSignal
public import Mathlib.Data.Real.Basic

@[expose] public section

/-!
# The boundary `set` puts at the lower bound

The first part of `set.m` after the indices are found: the cell of the lower bound `lb` gets a
boundary at `lb`, unless its value is already `value` or `lb = 0`; if there already is one at
`lb`, nothing is added, and if the cell before has the value, that boundary is dropped (`startIdx`
moves back). The result is the new `startIdx`, and the `newTim` and `newVal` so far.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       15-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The `startIdx`, `newTim` and `newVal` after the lower boundary; `startIdx` is `0`-based. -/
noncomputable def FiniteSignal.setLower {V : Type} [DecidableEq V] (s : FiniteSignal ℝ V)
    (a : ℝ) (value : V) (startIdx : ℕ) : ℕ × List ℝ × List V :=
  -- if val(startIdx) ~= value && lb > 0
  if s.value[startIdx]? ≠ some value ∧ 0 < a then
    -- if startIdx - 1 > 0 && tim(startIdx-1) == lb
    if 0 < startIdx ∧ s.time[startIdx - 1]? = some a then
      -- merge with previous interval by dropping the preceding time, or do nothing
      if s.value[startIdx - 1]? = some value then (startIdx - 1, [], []) else (startIdx, [], [])
    -- newTim = lb; newVal = val(startIdx)
    else (startIdx, [a], s.value[startIdx]?.toList)
  else (startIdx, [], [])

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
