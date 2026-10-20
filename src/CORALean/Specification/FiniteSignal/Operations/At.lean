module

public import CORALean.Specification.FiniteSignal.Operations.ValueAt
public import CORALean.Specification.FiniteSignal.FiniteSignal
public import CORALean.Specification.FiniteSignal.Operations.Basic

@[expose] public section

/-!
# The value at a time

`val = at(sig,time)` of `at.m`: CORA throws if the time is beyond the duration (or negative); here
`none`.

## Inputs
* `T` – time type
* `V` – value type
* `s` – signal
* `t` – time

## Output
* the value at the time, or none if out of range
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `val = at(sig,time)`. -/
def FiniteSignal.at? {T V : Type} [LinearOrder T] [Zero T] (s : FiniteSignal T V) (t : T) :
    Option V :=
  -- 1. the time must lie in the range of the signal
  if 0 ≤ t ∧ t ≤ s.duration then
    -- 2. i = the first index with time(i) > t, the last index if there is none
    let i := min (s.time.takeWhile (· ≤ t)).length (s.length - 1)
    -- 3. val = sig.value(i)
    s.value[i]?
  else none

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
