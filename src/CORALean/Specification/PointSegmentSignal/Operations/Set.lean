module

public import CORALean.Global.IsEqvTop
public import CORALean.Specification.PointSegmentSignal.Operations.AtIdx
public import CORALean.Specification.PointSegmentSignal.Operations.Basic
public import CORALean.Specification.PointSegmentSignal.Operations.SetPoint
public import CORALean.Specification.STLInterval.Operations.Basic
public import CORALean.Global.StepOf

@[expose] public section

/-!
# Setting the value in an interval

`set(obj,interval,value)` of `pointSegmentSignal.m` for a time scalar `𝕋` and an `stlInterval`: the
interval's bounds and closedness flags are read off (`lowerBound`, `upperBound`) and
`step_setBounds` does the work.

## Inputs
* `s` – signal
* `I` – time interval
* `value` – value to set

## Output
* the signal with the value set on the interval
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

variable {𝕋 : Type} [Float.FloatOps 𝕋] [Float.SoundFloatArithmetic 𝕋] [TimeOrder 𝕋]


-- ------------------------------------------  STEPS  ------------------------------------------- --

/-- `step_isNewPointOk(obj,i,p,vals)`. -/
@[step_of PointSegmentSignal.set]
def PointSegmentSignal.step_isNewPointOk {T : Type} [TimeOrder T] [Zero T]
    (s : PointSegmentSignal T) (i : ℕ) (p : T) (vals : List Bool) : Bool :=
  if TimeOrder.Eqv (s.timePoints.getD (i - 1) 0) p then
    TimeOrder.Eqv p 0 ∨ vals.getD 0 false ≠ vals.getD 1 false ∨
      vals.getD 0 false ≠ s.precIntervalValue i
  else vals.any (fun v => v ≠ s.succIntervalValue i)

/-- `sig = set(obj,stlInterval(lb,ub,lc,rc),value)`. -/
@[step_of PointSegmentSignal.set]
def PointSegmentSignal.step_setBounds {T : Type} [TimeOrder T] [Zero T] (s : PointSegmentSignal T)
    (lb : T) (ub : WithTop T) (lc rc : Bool) (value : Bool) : PointSegmentSignal T :=
  if STLInterval.emptyBounds lb ub lc rc then s
  else if TimeOrder.IsEqvTop (lb : WithTop T) ub then s.setPoint lb value
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
    let addL := s.step_isNewPointOk i lb lVal
    let addR := rVal.any (fun v => v ≠ value) ∧ ub ≠ ⊤
    let newPoints := (if addL then [lb] else []) ++ (if addR then [ub.untopD 0] else [])
    let newValues := (if addL then lVal else []) ++ (if addR then rVal else [])
    -- 4. an old point at lb is replaced
    let i' := if TimeOrder.Eqv (s.timePoints.getD (i - 1) 0) lb then i - 1 else i
    -- 5. keep the points before and after, drop those inside
    ⟨s.timePoints.take i' ++ newPoints ++ s.timePoints.drop j,
      s.values.take (2 * i') ++ newValues ++ s.values.drop (2 * j)⟩


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `sig = set(obj,interval,value)`. -/
def PointSegmentSignal.set (s : PointSegmentSignal 𝕋) (I : STLInterval 𝕋) (value : Bool) :
    PointSegmentSignal 𝕋 :=
  s.step_setBounds I.lowerBound I.upperBound I.lowerClosed I.upperClosed value

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
