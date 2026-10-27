module

public import CORALean.Specification.FiniteSignal.FiniteSignal
public import CORALean.Specification.FiniteSignal.Operations.Basic
public import CORALean.ContSet.Interval.Real.Interval
public import CORALean.Global.StepOf

@[expose] public section

/-!
# The maximal intervals where a condition holds

`int = findIntervals(sig,cond)` of `findIntervals.m`: the disjoint closed intervals `[start,
stop]` of the maximal runs of cells whose value satisfies `cond` (CORA returns `interval` objects,
the empty array if there is none; here `Interval`s and the empty list). The first interval
starts at `0` if the first value satisfies `cond`; `start` is unset before, and set by a rising
edge before it is first read.

## Inputs
* `T` – time type
* `V` – value type
* `s` – signal
* `cond` – condition on values

## Output
* the maximal closed intervals where the condition holds
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean


-- ------------------------------------------  STEPS  ------------------------------------------- --

/-- The intervals `[start, time(i)]` that the loop adds for the breakpoints `L`. -/
@[step_of FiniteSignal.findIntervals]
def FiniteSignal.step_findIntervalsLoop {T V : Type} (cond : V → Bool) (start : T) :
    List (T × V) → List (Real.Interval T)
  | [] => []
  -- last interval may hold until end of signal
  | [(t, v)] => if cond v then [⟨start, t⟩] else []
  | (t, v) :: (t', v') :: rest =>
    -- rising edge: ~cond(value(i)) && cond(value(i+1))
    let start' := if !cond v && cond v' then t else start
    -- falling edge: cond(value(i)) && ~cond(value(i+1))
    (if cond v && !cond v' then [⟨start, t⟩] else []) ++
      FiniteSignal.step_findIntervalsLoop cond start' ((t', v') :: rest)


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `int = findIntervals(sig,cond)`. -/
def FiniteSignal.findIntervals {T V : Type} [Zero T] (s : FiniteSignal T V) (cond : V → Bool) :
    List (Real.Interval T) :=
  -- if cond(sig.value(1)) then start = 0
  FiniteSignal.step_findIntervalsLoop cond 0 s.pairs

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
