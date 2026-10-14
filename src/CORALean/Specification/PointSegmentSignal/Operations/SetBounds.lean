module

public import CORALean.Specification.PointSegmentSignal.Operations.AtIdx
public import CORALean.Specification.PointSegmentSignal.Operations.IsNewPointOk
public import CORALean.Specification.PointSegmentSignal.Operations.SetPoint
public import CORALean.Specification.STLInterval.Operations.Basic

@[expose] public section

/-!
# Setting the value in a time interval

`set(obj,interval,value)` of `pointSegmentSignal.m`: set the signal to `value` on the interval. An
empty interval changes nothing and a single time is `aux_setPoint`. Otherwise the points of the
signal inside the interval are replaced by new ones at its ends (`lb`, `ub`) with the values on
either side, unless a new point would be redundant, and the signal keeps the part before and after.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `sig = set(obj,stlInterval(lb,ub,lc,rc),value)`. -/
def PointSegmentSignal.setBounds {T : Type} [LinearOrder T] [Zero T] (s : PointSegmentSignal T)
    (lb : T) (ub : WithTop T) (lc rc : Bool) (value : Bool) : PointSegmentSignal T :=
  if STLInterval.emptyBounds lb ub lc rc then s
  else if (lb : WithTop T) = ub then s.setPoint lb value
  else
    -- 1. [before,i] = priv_atIdx(obj,lb) and [afterPoint,j] = priv_atIdx(obj,ub)
    let before := (s.atIdx lb).1
    let i := (s.atIdx lb).2
    let afterPoint := (s.atIdx ub).1
    let j := (s.atIdx ub).2
    let after := s.succIntervalValue j
    -- 2. the point and interval values at the two ends of the new interval
    let lVal := if lc then [value, value] else [before, value]
    let rVal := if rc then [value, after] else [afterPoint, after]
    -- 3. new points at the ends, where they are needed
    let addL := s.isNewPointOk i lb lVal
    let addR := rVal.any (fun v => v ≠ value) ∧ ub ≠ ⊤
    let newPoints := (if addL then [lb] else []) ++ (if addR then [ub.untopD 0] else [])
    let newValues := (if addL then lVal else []) ++ (if addR then rVal else [])
    -- 4. an old point at lb is replaced
    let i' := if s.timePoints.getD (i - 1) 0 = lb then i - 1 else i
    -- 5. keep the points before and after, drop those inside
    ⟨s.timePoints.take i' ++ newPoints ++ s.timePoints.drop j,
      s.values.take (2 * i') ++ newValues ++ s.values.drop (2 * j)⟩

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
