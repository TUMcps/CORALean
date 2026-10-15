module

public import CORALean.Specification.FiniteSignal.FiniteSignal

@[expose] public section

/-!
# The loop of `findIntervals`

The loop of `findIntervals.m` over the breakpoints, with the variable `start` as an argument: the
body at `i` looks at the values at `i` and `i+1` and, on a rising edge, remembers `time(i)` as the
start; on a falling edge it adds the interval `[start, time(i)]`. The last breakpoint closes a run
that holds until the end of the signal.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The intervals `[start, time(i)]` that the loop adds for the breakpoints `L`. -/
def FiniteSignal.findIntervalsLoop {T V : Type} (cond : V → Bool) (start : T) :
    List (T × V) → List (T × T)
  | [] => []
  -- last interval may hold until end of signal
  | [(t, v)] => if cond v then [(start, t)] else []
  | (t, v) :: (t', v') :: rest =>
    -- rising edge: ~cond(value(i)) && cond(value(i+1))
    let start' := if !cond v && cond v' then t else start
    -- falling edge: cond(value(i)) && ~cond(value(i+1))
    (if cond v && !cond v' then [(start, t)] else []) ++
      FiniteSignal.findIntervalsLoop cond start' ((t', v') :: rest)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
