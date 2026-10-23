module

public import CORALean.Global.Interfaces
public import CORALean.Specification.FiniteSignal.FiniteSignal
public import CORALean.Specification.FiniteSignal.Operations.Basic

@[expose] public section

/-!
# The maximum of a signal on an interval

`val = max(sig,int)` of `max.m`, for values that are ordered and have a `0` (CORA starts from `val
= 0`): the first loop finds the first breakpoint with `time(i) >= infimum(int)` and takes its
value, the second takes the value after every breakpoint with `time(j) <= supremum(int)` from
there on. The interval `int` is given by its bounds `lo` and `hi`, time stamps like the signal's.
A signal that ends before `lo` has maximum `0`. Generic over the time type: at a float scalar the
comparisons are exact (`TimeOrder`), so nothing rounds.

## Inputs
* `T` – time type
* `V` – value type
* `s` – signal
* `lo` – interval lower bound
* `hi` – interval upper bound

## Output
* the maximum of the signal on the interval
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `val = max(sig,int)`. -/
protected def FiniteSignal.max {T V : Type} [TimeOrder T] [Zero T] [LinearOrder V] [Zero V]
    (s : FiniteSignal T V) (lo hi : T) : V :=
  -- find index where interval begins: i = first index with time(i) >= infimum(int)
  let i := (s.time.takeWhile (fun t => decide (t < lo))).length
  -- val = max(val, sig.value(i)), or 0 if there is no such index
  let val := match s.value[i]? with
    | some v => Max.max 0 v
    | none => 0
  -- continue while interval lasts: for j = i:length(sig)-1, if time(j) <= supremum(int)
  (List.range' i (s.length - 1 - i)).foldl (fun val j =>
    if s.time.getD j 0 ≤ hi then Max.max val (s.value.getD (j + 1) 0) else val) val

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
