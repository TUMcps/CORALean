module

public import CORALean.Specification.FiniteSignal.FiniteSignal
public import CORALean.Specification.FiniteSignal.Operations.Basic
public import CORALean.Specification.FiniteSignal.Operations.Mk
public import Mathlib.Data.EReal.Operations
public import Mathlib.Data.Real.Basic

@[expose] public section

/-!
# Setting the value on an interval

`sig = set(obj,interval,value)` of `set.m`: the signal with `value` from the interval's lower
bound (at least `0`) up to its upper bound (at most the duration), boundaries merged with equal
neighbours; the closedness flags are not read. CORA throws for an empty or singleton interval, for
one at or beyond the end of the signal (`startIdx` is empty), or if the constructor fails; all are
`none`, as is an interval before `0`.
Refinement pending: CORA computes this in doubles, its refinement over `𝕋` is not yet written.

## Inputs
* `V` – value type
* `s` – signal
* `lo` – interval lower bound
* `hi` – interval upper bound
* `value` – value to set

## Output
* the signal with the value set on the interval, or none
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       15-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- The `startIdx`, `newTim` and `newVal` after the lower boundary; `startIdx` is `0`-based. -/
noncomputable def FiniteSignal.aux_setLower {V : Type} [DecidableEq V] (s : FiniteSignal ℝ V)
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


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `sig = set(obj,interval,value)`. -/
protected noncomputable def FiniteSignal.set? {V : Type} [DecidableEq V] (s : FiniteSignal ℝ V)
    (lo hi : EReal) (value : V) : Option (FiniteSignal ℝ V) :=
  -- lb = max(infimum(interval),0); ub = min(supremum(interval),obj.duration)
  let lb : EReal := Max.max lo 0
  let ub : EReal := Min.min hi (s.duration : EReal)
  -- no empty or singleton intervals are allowed
  if ¬ lb < ub then none
  else
    -- startIdx = find(obj.time > lb,1); stopIdx = find(obj.time > ub,1)
    let startIdx := (s.time.takeWhile (· ≤ lb.toReal)).length
    let stopIdx := (s.time.takeWhile (· ≤ ub.toReal)).length
    -- the boundary at the lower bound
    let lower := s.aux_setLower lb.toReal value startIdx
    -- if ub == obj.duration || val(stopIdx) ~= value, a boundary at the upper bound
    let upper := ub.toReal = s.duration ∨ s.value[stopIdx]? ≠ some value
    let newTim := if upper then lower.2.1 ++ [ub.toReal] else lower.2.1
    let newVal := if upper then lower.2.2 ++ [value] else lower.2.2
    -- tim = [tim(1:startIdx-1), newTim, tim(stopIdx:end)], and the same for val
    FiniteSignal.mk? (s.time.take lower.1 ++ newTim ++ s.time.drop stopIdx)
      (s.value.take lower.1 ++ newVal ++ s.value.drop stopIdx)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
