module

public import CORALean.Global.IsEqvTop
public import CORALean.Specification.PointSegmentSignal.Operations.Basic
public import CORALean.Specification.PointSegmentSignal.Operations.SuccTimeAtValIdx

@[expose] public section

/-!
# The end of the last stretch with a value

`[time,inclusive] = findLast(obj,value)` of `pointSegmentSignal`: the end of the last stored value
equal to `value`, as a time (`inf` as `⊤`) and whether the signal still has the value at that time.
If no value is `value`, it is `0` and not inclusive.

## Inputs
* `T` – time type
* `s` – signal
* `value` – value to find

## Output
* the end of the last stretch with that value and whether it is inclusive
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `[time,inclusive] = findLast(obj,value)`. -/
def PointSegmentSignal.findLast {T : Type} [TimeOrder T] [Zero T] (s : PointSegmentSignal T)
    (value : Bool) : WithTop T × Bool :=
  -- 1. i = find(obj.values == value,1,'last')
  match (List.matlabFind (· == value) s.values).getLast? with
  | none => (((0 : T) : WithTop T), false)
  -- 2. the end of the value `i`
  | some i => s.succTimeAtValIdx i

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
