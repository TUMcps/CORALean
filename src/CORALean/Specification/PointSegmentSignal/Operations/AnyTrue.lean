module

public import CORALean.Global.IsEqvTop
public import CORALean.Specification.PointSegmentSignal.Operations.Basic
public import CORALean.Specification.PointSegmentSignal.Operations.RelevantStart
public import CORALean.Specification.PointSegmentSignal.Operations.RelevantStop

@[expose] public section

/-!
# Whether some value in an interval satisfies a condition

`anyTrue(obj,interval,cond)` of `pointSegmentSignal.m`: `cond` holds of some stored value that the
signal takes at a time of the interval, found as the values from `start` to `stop`
(`priv_relevantValueIdx`). The defaults are the whole time axis and the identity.

## Inputs
* `T` – time type
* `s` – signal
* `lb` – interval lower bound
* `ub` – interval upper bound
* `lc` – lower bound is closed
* `rc` – upper bound is closed
* `cond` – condition on values

## Output
* whether some value in the interval satisfies the condition
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `res = anyTrue(obj,interval,cond)`. -/
def PointSegmentSignal.anyTrue {T : Type} [TimeOrder T] [Zero T] (s : PointSegmentSignal T)
    (lb : T := 0) (ub : WithTop T := ⊤) (lc : Bool := true) (rc : Bool := false)
    (cond : Bool → Bool := id) : Bool :=
  -- res = any(arrayfun(cond,obj.values(start:stop))), [start,stop] = priv_relevantValueIdx(...)
  ((s.values.take (s.relevantStop ub rc)).drop (s.relevantStart lb lc - 1)).any cond

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
