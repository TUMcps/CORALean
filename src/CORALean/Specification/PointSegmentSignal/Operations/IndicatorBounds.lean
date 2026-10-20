module

public import CORALean.Specification.PointSegmentSignal.PointSegmentSignal
public import CORALean.Specification.STLInterval.Operations.Basic
public import Mathlib.Algebra.Group.Defs

@[expose] public section

/-!
# Indicator signals

`indicator(interval,val,default)` of `pointSegmentSignal.m`: the signal that is `val` on the
interval and `default` elsewhere. The interval's ends become the time points, each point taking
`val` when its end is closed. The interval must start at a time `≥ 0` (the `stlInterval` constructor
guarantees it).

## Inputs
* `T` – time type
* `lb` – interval lower bound
* `ub` – interval upper bound
* `lc` – lower bound is closed
* `rc` – upper bound is closed
* `val` – value on the interval
* `default` – value elsewhere

## Output
* the signal that is `val` on the interval and `default` elsewhere
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `sig = pointSegmentSignal.indicator(stlInterval(lb,ub,lc,rc),val,default)`. -/
def PointSegmentSignal.indicatorBounds {T : Type} [LinearOrder T] [Zero T] (lb : T)
    (ub : WithTop T) (lc rc : Bool) (val default : Bool) : PointSegmentSignal T :=
  if val = default ∨ STLInterval.emptyBounds lb ub lc rc = true then ⟨[0], [default, default]⟩
  else
    -- 1. set signal in [0,infi)
    let tp1 : List T := if 0 < lb then [0] else []
    let v1 : List Bool := if 0 < lb then [default, default] else []
    -- 2. set signal at infi
    let tp2 := tp1 ++ [lb]
    let v2 := v1 ++ [if lc then val else default]
    -- 3. set signal in (infi,sup)
    let v3 := if (lb : WithTop T) ≠ ub then v2 ++ [val] else v2
    -- 4. set signal at sup
    let atSup := (lb : WithTop T) ≠ ub ∧ ub ≠ ⊤
    let tp4 := if atSup then tp2 ++ [ub.untopD 0] else tp2
    let v4 := if atSup then v3 ++ [if rc then val else default] else v3
    -- 5. set signal in (sup,inf)
    ⟨tp4, if ub ≠ ⊤ then v4 ++ [default] else v4⟩

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
