module

public import CORALean.Specification.FiniteSignal.FiniteSignal

@[expose] public section

/-!
# The cells between breakpoints

The cell of a breakpoint `(b,v)` is `[a,b]` with `a` the previous breakpoint (`0` for the first):
the times its value is valid, closed at both ends as `findIntervals.m` and `max.m` read them.

## Inputs
* `T` – time type
* `V` – value type

## Output
* the cells between consecutive breakpoints
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The cells `((a,b),v)` of the breakpoints `L` after the time `a`. -/
def FiniteSignal.cellsFrom {T V : Type} : T → List (T × V) → List ((T × T) × V)
  | _, [] => []
  | a, (b, v) :: rest => ((a, b), v) :: FiniteSignal.cellsFrom b rest

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
