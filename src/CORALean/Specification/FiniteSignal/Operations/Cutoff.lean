module

public import CORALean.Specification.FiniteSignal.FiniteSignal
public import CORALean.Specification.FiniteSignal.Operations.Basic
public import CORALean.Specification.FiniteSignal.Operations.Mk

@[expose] public section

/-!
# Cutting a signal off

`sig = cutoff(sig,dur)` of `cutoff.m`: the signal up to the duration `dur`, which CORA requires
not to exceed the signal's own. CORA throws there, and in the constructor if its checks fail (a
negative `dur`); both are `none`.

## Inputs
* `T` – time type
* `V` – value type
* `s` – signal
* `dur` – new duration

## Output
* the signal cut off at `dur`, or none if `dur` exceeds its duration
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `sig = cutoff(sig,dur)`. -/
def FiniteSignal.cutoff? {T V : Type} [TimeOrder T] [Zero T] [DecidableEq V]
    (s : FiniteSignal T V) (dur : T) : Option (FiniteSignal T V) :=
  -- the signal must have at least the given duration
  if s.duration < dur then none
  else
    -- find index where time exceeds duration: i = first index with time(i) >= dur
    let i := (s.time.takeWhile (· < dur)).length + 1
    -- construct cut signal
    FiniteSignal.mk? (s.time.take (i - 1) ++ [dur]) (s.value.take i)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
