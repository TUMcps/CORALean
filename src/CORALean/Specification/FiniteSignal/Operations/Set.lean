module

public import CORALean.Global.Interfaces
public import CORALean.Specification.FiniteSignal.FiniteSignal
public import CORALean.Specification.FiniteSignal.Operations.Basic
public import CORALean.Specification.FiniteSignal.Operations.Mk

@[expose] public section

/-!
# Setting the value on an interval

`sig = set(obj,interval,value)` of `set.m`: the signal with `value` from the interval's lower
bound (at least `0`) up to its upper bound (at most the duration), boundaries merged with equal
neighbours; the closedness flags are not read. CORA throws for an empty or singleton interval, for
one at or beyond the end of the signal (`startIdx` is empty), or if the constructor fails; all are
`none`, as is an interval before `0`. The bounds are time stamps like the signal's; an unbounded
end behaves as a bound outside `[0, duration]`. Generic over the time type: at a float scalar the
comparisons are exact (`TimeOrder`), so nothing rounds.

## Inputs
* `T` – time type
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
def FiniteSignal.aux_setLower {T V : Type} [TimeOrder T] [Zero T] [DecidableEq V]
    (s : FiniteSignal T V) (a : T) (value : V) (startIdx : ℕ) : ℕ × List T × List V :=
  -- if val(startIdx) ~= value && lb > 0
  if s.value[startIdx]? ≠ some value ∧ 0 < a then
    -- if startIdx - 1 > 0 && tim(startIdx-1) == lb
    if 0 < startIdx ∧ ∃ b ∈ s.time[startIdx - 1]?, TimeOrder.Eqv b a then
      -- merge with previous interval by dropping the preceding time, or do nothing
      if s.value[startIdx - 1]? = some value then (startIdx - 1, [], []) else (startIdx, [], [])
    -- newTim = lb; newVal = val(startIdx)
    else (startIdx, [a], s.value[startIdx]?.toList)
  else (startIdx, [], [])


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `sig = set(obj,interval,value)`. -/
protected def FiniteSignal.set? {T V : Type} [TimeOrder T] [Zero T] [DecidableEq V]
    (s : FiniteSignal T V) (lo hi : T) (value : V) : Option (FiniteSignal T V) :=
  -- lb = max(infimum(interval),0); ub = min(supremum(interval),obj.duration)
  let lb : T := if lo ≤ 0 then 0 else lo
  let ub : T := if hi ≤ s.duration then hi else s.duration
  -- no empty or singleton intervals are allowed
  if ¬ lb < ub then none
  else
    -- startIdx = find(obj.time > lb,1); stopIdx = find(obj.time > ub,1)
    let startIdx := (s.time.takeWhile (· ≤ lb)).length
    let stopIdx := (s.time.takeWhile (· ≤ ub)).length
    -- the boundary at the lower bound
    let lower := s.aux_setLower lb value startIdx
    -- if ub == obj.duration || val(stopIdx) ~= value, a boundary at the upper bound
    let upper := TimeOrder.Eqv ub s.duration ∨ s.value[stopIdx]? ≠ some value
    let newTim := if upper then lower.2.1 ++ [ub] else lower.2.1
    let newVal := if upper then lower.2.2 ++ [value] else lower.2.2
    -- tim = [tim(1:startIdx-1), newTim, tim(stopIdx:end)], and the same for val
    FiniteSignal.mk? (s.time.take lower.1 ++ newTim ++ s.time.drop stopIdx)
      (s.value.take lower.1 ++ newVal ++ s.value.drop stopIdx)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
